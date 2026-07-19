"""
CPTP residual block — Phase 2: against strong baselines.

Phase 1 (cptp_depth.py) showed CPTPBlock was the only architecture above
the 8-class random floor at depth 32. Phase 2 tests that claim against
modern stabilizers (RMSNorm, ReZero, DeepNorm, gated residuals) and
includes a CPTP-readout-no-iteration control to isolate whether the win
comes from the channel iteration or just from the diagonal readout.

Architectures:
  (A) StandardPreLN          x ← LN(x + MLP(x))                 — Phase 1
  (B) StandardNoNorm         x ← x + MLP(x)                     — Phase 1
  (C) RMSNorm                x ← RMSNorm(x + MLP(x))            — new
  (D) ReZero                 x ← x + γ * MLP(x), γ init 0       — new
  (E) DeepNorm               x ← LN(α*x + MLP(x)), α scaled     — new
  (F) GatedResidual          x ← (1-σ(g))*x + σ(g)*MLP(x)       — new
  (G) CPTPBlock              ρ ← Σ K_i ρ K_i^T                  — Phase 1
  (H) CPTPReadoutOnly        encode→ρ→diagonal head, NO iter    — control

If (G) >> (H) at large L: channel iteration is doing real work.
If (G) ≈ (H): the readout asymmetry is doing the work, not the iteration.
"""

import math
import torch
import torch.nn as nn
import torch.nn.functional as F


# ---------------- Data (same as Phase 1) ----------------

def make_task(n_classes=8, embed_dim=16, n_samples=4096, noise=1.0, seed=0):
    g = torch.Generator().manual_seed(seed)
    prototypes = torch.randn(n_classes, embed_dim, generator=g)
    prototypes = F.normalize(prototypes, dim=-1) * 3.0
    y = torch.randint(0, n_classes, (n_samples,), generator=g)
    x = prototypes[y] + noise * torch.randn(n_samples, embed_dim, generator=g)
    return x, y


# ---------------- Architectures ----------------

class _SharedMLP(nn.Module):
    def __init__(self, dim, hidden):
        super().__init__()
        self.f = nn.Sequential(
            nn.Linear(dim, hidden), nn.GELU(), nn.Linear(hidden, dim)
        )
    def forward(self, x): return self.f(x)


class StandardPreLN(nn.Module):
    def __init__(self, dim, hidden, depth, n_classes):
        super().__init__()
        self.enc = nn.Linear(dim, dim); self.ln = nn.LayerNorm(dim)
        self.mlp = _SharedMLP(dim, hidden); self.head = nn.Linear(dim, n_classes)
        self.depth = depth
    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth): x = self.ln(x + self.mlp(x))
        return self.head(x)


class StandardNoNorm(nn.Module):
    def __init__(self, dim, hidden, depth, n_classes):
        super().__init__()
        self.enc = nn.Linear(dim, dim); self.mlp = _SharedMLP(dim, hidden)
        self.head = nn.Linear(dim, n_classes); self.depth = depth
    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth): x = x + self.mlp(x)
        return self.head(x)


class RMSNorm(nn.Module):
    """x ← RMSNorm(x + MLP(x))."""
    def __init__(self, dim, hidden, depth, n_classes, eps=1e-6):
        super().__init__()
        self.enc = nn.Linear(dim, dim); self.mlp = _SharedMLP(dim, hidden)
        self.gain = nn.Parameter(torch.ones(dim))
        self.head = nn.Linear(dim, n_classes); self.depth = depth; self.eps = eps
    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth):
            x = x + self.mlp(x)
            rms = x.pow(2).mean(dim=-1, keepdim=True).add(self.eps).sqrt()
            x = self.gain * x / rms
        return self.head(x)


class ReZero(nn.Module):
    """x ← x + γ * MLP(x), γ init 0 (Bachlechner et al., 2020)."""
    def __init__(self, dim, hidden, depth, n_classes):
        super().__init__()
        self.enc = nn.Linear(dim, dim); self.mlp = _SharedMLP(dim, hidden)
        self.gamma = nn.Parameter(torch.zeros(1))
        self.head = nn.Linear(dim, n_classes); self.depth = depth
    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth): x = x + self.gamma * self.mlp(x)
        return self.head(x)


class DeepNorm(nn.Module):
    """x ← LN(α*x + MLP(x)), α = (2L)^(1/4) (Wang et al., 2022)."""
    def __init__(self, dim, hidden, depth, n_classes):
        super().__init__()
        self.enc = nn.Linear(dim, dim); self.ln = nn.LayerNorm(dim)
        self.mlp = _SharedMLP(dim, hidden); self.head = nn.Linear(dim, n_classes)
        self.depth = depth
        self.alpha = (2 * depth) ** 0.25
    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth): x = self.ln(self.alpha * x + self.mlp(x))
        return self.head(x)


class GatedResidual(nn.Module):
    """x ← (1-σ(g(x))) * x + σ(g(x)) * MLP(x), gate from input."""
    def __init__(self, dim, hidden, depth, n_classes):
        super().__init__()
        self.enc = nn.Linear(dim, dim); self.mlp = _SharedMLP(dim, hidden)
        self.gate = nn.Linear(dim, dim); self.head = nn.Linear(dim, n_classes)
        self.depth = depth
    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth):
            g = torch.sigmoid(self.gate(x)); x = (1 - g) * x + g * self.mlp(x)
        return self.head(x)


class CPTPBlock(nn.Module):
    """ρ ← Σ_i K_i ρ K_i^T, Σ K_i^T K_i = I via QR (real, shared, iterated)."""
    def __init__(self, dim, num_kraus, depth, n_classes):
        super().__init__()
        self.d = dim; self.k = num_kraus; self.depth = depth
        self.enc = nn.Linear(dim, dim)
        self.raw = nn.Parameter(torch.randn(num_kraus * dim, dim) * 0.5)
        self.head = nn.Linear(dim, n_classes)
    def _kraus(self):
        Q, _ = torch.linalg.qr(self.raw); return Q.reshape(self.k, self.d, self.d)
    def forward(self, x):
        v = self.enc(x); v = v / (v.norm(dim=-1, keepdim=True) + 1e-8)
        rho = torch.einsum('bi,bj->bij', v, v)
        K = self._kraus()
        for _ in range(self.depth):
            K_rho = torch.einsum('kij,bjl->bkil', K, rho)
            new_rho = torch.einsum('bkij,kjl->bkil', K_rho, K.transpose(-1,-2))
            rho = 0.5 * (new_rho.sum(dim=1) + new_rho.sum(dim=1).transpose(-1,-2))
        p = torch.diagonal(rho, dim1=-2, dim2=-1)
        return self.head(p)


class CPTPReadoutOnly(nn.Module):
    """Control: encoder → rank-1 ρ → diagonal → head. NO channel iteration.
    Distinguishes whether CPTPBlock's win is from iteration or just readout."""
    def __init__(self, dim, num_kraus, depth, n_classes):
        super().__init__()
        self.d = dim; self.enc = nn.Linear(dim, dim)
        # Same param count as CPTPBlock: include the same Kraus stack as dead weight
        self.raw = nn.Parameter(torch.randn(num_kraus * dim, dim) * 0.5)
        self.head = nn.Linear(dim, n_classes)
    def forward(self, x):
        v = self.enc(x); v = v / (v.norm(dim=-1, keepdim=True) + 1e-8)
        rho = torch.einsum('bi,bj->bij', v, v)
        p = torch.diagonal(rho, dim1=-2, dim2=-1)
        return self.head(p)


# ---------------- Training ----------------

def count_params(m): return sum(p.numel() for p in m.parameters())


def train(model, x_train, y_train, x_eval, y_eval, epochs=120, bs=256, lr=3e-3):
    opt = torch.optim.Adam(model.parameters(), lr=lr)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=epochs)
    n = x_train.shape[0]
    for _ in range(epochs):
        perm = torch.randperm(n)
        for i in range(0, n, bs):
            idx = perm[i:i+bs]
            logits = model(x_train[idx])
            loss = F.cross_entropy(logits, y_train[idx])
            opt.zero_grad(); loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            opt.step()
        sched.step()
    with torch.no_grad():
        logits = model(x_eval)
        if not torch.isfinite(logits).all(): return 0.0
        return (logits.argmax(-1) == y_eval).float().mean().item()


def main():
    DIM, N_CLASSES, HIDDEN, NUM_KRAUS = 16, 8, 32, 4
    DEPTHS = [2, 8, 32]
    SEEDS = [0, 1, 2]

    torch.manual_seed(0)
    x_train, y_train = make_task(N_CLASSES, DIM, n_samples=4096, seed=10)
    x_eval, y_eval = make_task(N_CLASSES, DIM, n_samples=1024, seed=20)

    archs = [
        ("StandardPreLN",   lambda d: StandardPreLN(DIM, HIDDEN, d, N_CLASSES)),
        ("StandardNoNorm",  lambda d: StandardNoNorm(DIM, HIDDEN, d, N_CLASSES)),
        ("RMSNorm",         lambda d: RMSNorm(DIM, HIDDEN, d, N_CLASSES)),
        ("ReZero",          lambda d: ReZero(DIM, HIDDEN, d, N_CLASSES)),
        ("DeepNorm",        lambda d: DeepNorm(DIM, HIDDEN, d, N_CLASSES)),
        ("GatedResidual",   lambda d: GatedResidual(DIM, HIDDEN, d, N_CLASSES)),
        ("CPTPBlock",       lambda d: CPTPBlock(DIM, NUM_KRAUS, d, N_CLASSES)),
        ("CPTPReadoutOnly", lambda d: CPTPReadoutOnly(DIM, NUM_KRAUS, d, N_CLASSES)),
    ]

    print("Param counts (depth=8):", flush=True)
    for name, ctor in archs:
        print(f"  {name:18} {count_params(ctor(8)):>5d}", flush=True)
    print(f"\nRandom-chance baseline (8 classes): {1/N_CLASSES:.3f}", flush=True)
    print("(Read: 0.125 = pure random; below is worse-than-random.)\n", flush=True)

    results = {n: [] for n, _ in archs}
    for depth in DEPTHS:
        print(f"=== Depth L = {depth} ===", flush=True)
        for name, ctor in archs:
            accs = []
            for seed in SEEDS:
                torch.manual_seed(seed)
                accs.append(train(ctor(depth), x_train, y_train, x_eval, y_eval))
            mean = sum(accs) / len(accs)
            std = (sum((a-mean)**2 for a in accs) / len(accs)) ** 0.5
            results[name].append((depth, mean, std))
            marker = "**" if mean > 1/N_CLASSES else "  "
            print(f"  {marker} {name:18} {mean:.3f} ± {std:.3f}   "
                  f"seeds: {[f'{a:.3f}' for a in accs]}", flush=True)
        print(flush=True)

    print("=" * 78, flush=True)
    print("Phase 2 summary — test accuracy (mean ± std, 3 seeds). "
          f"** = above random {1/N_CLASSES:.3f}", flush=True)
    print("=" * 78, flush=True)
    print("arch              " + "  ".join(f"L={d:<13}" for d in DEPTHS), flush=True)
    for name in [n for n, _ in archs]:
        row = f"{name:18}"
        for _, mean, std in results[name]:
            mark = "*" if mean > 1/N_CLASSES else " "
            row += f"{mean:.3f}±{std:.3f}{mark}    "
        print(row, flush=True)


if __name__ == "__main__":
    main()
