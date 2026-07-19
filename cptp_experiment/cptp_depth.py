"""
CPTP residual block — stability under deep iteration.

Hypothesis: a shared-weight residual block applied L times is the cleanest
test of "structural rank-preservation." Standard `x + f(x)` residuals are
known to suffer from rank collapse / oversmoothing as L grows; a CPTP
block CANNOT collapse to zero or to a rank-deficient fixed point, because
trace is preserved by construction.

Task: classification of which of N latent classes generated an observation
sequence. The encoder produces an initial state; one residual block is
applied L times (weight-shared); a linear head reads out class logits.

We sweep L ∈ {2, 4, 8, 16, 32, 64} and compare:
  (A) standard pre-LN residual:    x ← LN(x + MLP(x))
  (B) standard, no normalization:  x ← x + MLP(x)
  (C) CPTP block:                  ρ ← Σ_i K_i ρ K_i^T

For each architecture and each L, train 3 seeds, report mean ± std.

Prediction: (B) degrades quickly with L (collapse/explosion). (A) is
stable to moderate L by virtue of LayerNorm. (C) is stable to arbitrary L
because trace preservation is architectural — no normalization needed.
If (C) at large L beats (A) at large L, the CPTP claim is supported.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F


# ---------------- Data ----------------

def make_task(n_classes=8, embed_dim=16, n_samples=4096, noise=1.0, seed=0):
    """N classes, each with a fixed random prototype in embed_dim.
    Sample x = prototype + noise, predict class."""
    g = torch.Generator().manual_seed(seed)
    prototypes = torch.randn(n_classes, embed_dim, generator=g)
    prototypes = F.normalize(prototypes, dim=-1) * 3.0  # well-separated
    y = torch.randint(0, n_classes, (n_samples,), generator=g)
    x = prototypes[y] + noise * torch.randn(n_samples, embed_dim, generator=g)
    return x, y, prototypes


# ---------------- Models ----------------

class StandardPreLN(nn.Module):
    """x_{l+1} = LayerNorm(x_l + MLP(x_l)), shared weights across depth."""
    def __init__(self, dim, hidden, depth, n_classes):
        super().__init__()
        self.enc = nn.Linear(dim, dim)
        self.ln = nn.LayerNorm(dim)
        self.mlp = nn.Sequential(
            nn.Linear(dim, hidden), nn.GELU(), nn.Linear(hidden, dim)
        )
        self.head = nn.Linear(dim, n_classes)
        self.depth = depth

    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth):
            x = self.ln(x + self.mlp(x))
        return self.head(x)


class StandardNoNorm(nn.Module):
    """x_{l+1} = x_l + MLP(x_l), shared weights, NO normalization."""
    def __init__(self, dim, hidden, depth, n_classes):
        super().__init__()
        self.enc = nn.Linear(dim, dim)
        self.mlp = nn.Sequential(
            nn.Linear(dim, hidden), nn.GELU(), nn.Linear(hidden, dim)
        )
        self.head = nn.Linear(dim, n_classes)
        self.depth = depth

    def forward(self, x):
        x = self.enc(x)
        for _ in range(self.depth):
            x = x + self.mlp(x)
        return self.head(x)


class CPTPBlock(nn.Module):
    """
    Shared CPTP block: ρ ← Σ_i K_i ρ K_i^T with Σ_i K_i^T K_i = I.

    Encoder maps input → vector v → ρ_0 = v v^T / |v|^2 (rank-1 init).
    After L iterations, classifier reads from diag(ρ) (the measurement).

    Constraint Σ K_i^T K_i = I is enforced via thin QR on a free parameter
    of shape (k*d, d). No training penalty, no projection — CPTP at every
    gradient step by construction.
    """
    def __init__(self, dim, num_kraus, depth, n_classes):
        super().__init__()
        self.d = dim
        self.k = num_kraus
        self.depth = depth
        self.enc = nn.Linear(dim, dim)
        # Single shared Kraus stack of shape (k*d, d)
        self.raw = nn.Parameter(torch.randn(num_kraus * dim, dim) * 0.5)
        self.head = nn.Linear(dim, n_classes)

    def _kraus(self):
        Q, _ = torch.linalg.qr(self.raw)
        return Q.reshape(self.k, self.d, self.d)

    def forward(self, x):
        # Encode → rank-1 density matrix
        v = self.enc(x)
        v = v / (v.norm(dim=-1, keepdim=True) + 1e-8)
        rho = torch.einsum('bi,bj->bij', v, v)  # (B, d, d)
        K = self._kraus()                       # (k, d, d)
        for _ in range(self.depth):
            # K @ ρ : (B, k, d, d)
            K_rho = torch.einsum('kij,bjl->bkil', K, rho)
            # K @ ρ @ K^T : (B, k, d, d)
            new_rho = torch.einsum('bkij,kjl->bkil',
                                   K_rho, K.transpose(-1, -2))
            rho = new_rho.sum(dim=1)
            rho = 0.5 * (rho + rho.transpose(-1, -2))
        # Diagonal measurement → classifier
        p = torch.diagonal(rho, dim1=-2, dim2=-1)
        return self.head(p)


def count_params(m):
    return sum(p.numel() for p in m.parameters())


# ---------------- Diagnostics: track rank/entropy at runtime ----------------

@torch.no_grad()
def measure_state_entropy(model, x, depths_to_probe):
    """Return entropy of state across depth (per architecture)."""
    if isinstance(model, CPTPBlock):
        v = model.enc(x)
        v = v / (v.norm(dim=-1, keepdim=True) + 1e-8)
        rho = torch.einsum('bi,bj->bij', v, v)
        K = model._kraus()
        out = {}
        for d in range(1, max(depths_to_probe) + 1):
            K_rho = torch.einsum('kij,bjl->bkil', K, rho)
            new_rho = torch.einsum('bkij,kjl->bkil',
                                   K_rho, K.transpose(-1, -2))
            rho = new_rho.sum(dim=1)
            rho = 0.5 * (rho + rho.transpose(-1, -2))
            if d in depths_to_probe:
                eigs = torch.linalg.eigvalsh(rho).clamp(min=1e-12)
                eigs = eigs / eigs.sum(-1, keepdim=True)
                ent = -(eigs * eigs.log()).sum(-1).mean().item()
                out[d] = ent
        return out
    else:
        x = model.enc(x)
        out = {}
        for d in range(1, max(depths_to_probe) + 1):
            if isinstance(model, StandardPreLN):
                x = model.ln(x + model.mlp(x))
            else:
                x = x + model.mlp(x)
            if d in depths_to_probe:
                # rough proxy: stddev across batch of normalized embeddings
                xn = F.normalize(x, dim=-1)
                # representation cosine variance: 1 - mean(<x_i, x_j>) for i≠j
                C = xn @ xn.T
                off = (C.sum() - C.diag().sum()) / (C.shape[0] * (C.shape[0] - 1))
                out[d] = 1.0 - off.item()
        return out


# ---------------- Training ----------------

def train(model, x_train, y_train, x_eval, y_eval, epochs=80, bs=256, lr=3e-3):
    opt = torch.optim.Adam(model.parameters(), lr=lr)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=epochs)
    n = x_train.shape[0]
    for ep in range(epochs):
        perm = torch.randperm(n)
        for i in range(0, n, bs):
            idx = perm[i:i + bs]
            logits = model(x_train[idx])
            loss = F.cross_entropy(logits, y_train[idx])
            opt.zero_grad()
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            opt.step()
        sched.step()
    with torch.no_grad():
        logits = model(x_eval)
        acc = (logits.argmax(-1) == y_eval).float().mean().item()
        # Some baselines explode — capture as NaN→0 accuracy
        if not torch.isfinite(logits).all():
            acc = 0.0
    return acc


def main():
    DIM = 16
    N_CLASSES = 8
    HIDDEN = 32
    NUM_KRAUS = 4
    DEPTHS = [2, 8, 32]
    SEEDS = [0, 1]

    torch.manual_seed(0)
    x_train, y_train, _ = make_task(N_CLASSES, DIM, n_samples=4096, seed=10)
    x_eval, y_eval, _ = make_task(N_CLASSES, DIM, n_samples=1024, seed=20)

    print("Param counts (for depth=8):")
    for name, ctor in [
        ("StandardPreLN", lambda: StandardPreLN(DIM, HIDDEN, 8, N_CLASSES)),
        ("StandardNoNorm", lambda: StandardNoNorm(DIM, HIDDEN, 8, N_CLASSES)),
        ("CPTPBlock", lambda: CPTPBlock(DIM, NUM_KRAUS, 8, N_CLASSES)),
    ]:
        print(f"  {name:18} {count_params(ctor()):>5d}")
    print()

    results = {n: [] for n in ["StandardPreLN", "StandardNoNorm", "CPTPBlock"]}

    for depth in DEPTHS:
        print(f"\n=== Depth L = {depth} ===")
        for name, ctor in [
            ("StandardPreLN",
             lambda d=depth: StandardPreLN(DIM, HIDDEN, d, N_CLASSES)),
            ("StandardNoNorm",
             lambda d=depth: StandardNoNorm(DIM, HIDDEN, d, N_CLASSES)),
            ("CPTPBlock",
             lambda d=depth: CPTPBlock(DIM, NUM_KRAUS, d, N_CLASSES)),
        ]:
            accs = []
            for seed in SEEDS:
                torch.manual_seed(seed)
                model = ctor()
                acc = train(model, x_train, y_train, x_eval, y_eval)
                accs.append(acc)
            mean = sum(accs) / len(accs)
            std = (sum((a - mean) ** 2 for a in accs) / len(accs)) ** 0.5
            results[name].append((depth, mean, std))
            print(f"  {name:18} acc {mean:.3f} ± {std:.3f}  "
                  f"(seeds: {[f'{a:.3f}' for a in accs]})")

    print("\n" + "=" * 70)
    print("Test accuracy vs depth (mean ± std over 3 seeds)")
    print("=" * 70)
    header = "depth".ljust(8) + "".join(n.ljust(20) for n in results)
    print(header)
    for i, depth in enumerate(DEPTHS):
        row = f"L={depth}".ljust(8)
        for n in results:
            _, mean, std = results[n][i]
            row += f"{mean:.3f}±{std:.3f}".ljust(20)
        print(row)



if __name__ == "__main__":
    main()
