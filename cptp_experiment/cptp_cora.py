"""
CPTP residual block — Phase 3: real graph benchmark (Cora).

2708-node citation graph, 7 classes, 1433-d sparse bag-of-words features.
Public Planetoid split (140 train / 500 val / 1000 test).

Task: deep iterative label propagation. Compare CPTP-Prop against the
strongest anti-oversmoothing baselines:

  (A) GCN+PreLN       — standard residual + LayerNorm
  (B) GCN+PairNorm    — Zhao & Akoglu 2020, the canonical
                        anti-oversmoothing baseline
  (C) APPNP           — Klicpera et al. 2019, personalized PageRank
                        propagation (initial-residual scheme)
  (D) GCN+GatedRes    — input-conditional gated residual
  (E) CPTP-Prop       — per-node density matrix ρ, neighborhood-
                        conditioned Kraus channel
  (F) CPTPReadoutOnly — control: encoder→ρ→diag→head, NO iteration

Diagnostics logged at each depth:
  - test accuracy
  - mean prediction entropy  (low = sharp, high = collapsed)
  - mean pairwise cosine of node states (high = oversmoothed)
  - effective rank of node-state matrix (low = collapsed)
  - between-class / within-class similarity ratio (low = separated)
"""

import math
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch_geometric.datasets import Planetoid


# ---------------- Cora ----------------

def load_cora():
    ds = Planetoid(root='/tmp/cora', name='Cora')
    d = ds[0]
    # Normalized adjacency (D^-1/2 (A+I) D^-1/2)
    n = d.num_nodes
    adj = torch.zeros(n, n)
    src, dst = d.edge_index
    adj[src, dst] = 1.0
    adj[dst, src] = 1.0
    adj.fill_diagonal_(1)
    deg = adj.sum(dim=1)
    d_inv_sqrt = deg.pow(-0.5)
    Ahat = adj * d_inv_sqrt[:, None] * d_inv_sqrt[None, :]
    return d.x, Ahat, d.y, d.train_mask, d.val_mask, d.test_mask, ds.num_classes


# ---------------- Shared layers ----------------

class _Propagate(nn.Module):
    def __init__(self, dim, hidden):
        super().__init__()
        self.W = nn.Linear(dim, hidden); self.U = nn.Linear(hidden, dim)
    def forward(self, x, Ahat):
        return self.U(F.gelu(self.W(Ahat @ x)))


# ---------------- Architectures ----------------

class GCN_PreLN(nn.Module):
    def __init__(self, in_dim, dim, hidden, depth, k):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim); self.ln = nn.LayerNorm(dim)
        self.prop = _Propagate(dim, hidden); self.head = nn.Linear(dim, k)
        self.depth = depth
    def forward(self, x, Ahat, return_state=False):
        x = self.enc(x)
        for _ in range(self.depth): x = self.ln(x + self.prop(x, Ahat))
        return (self.head(x), x) if return_state else self.head(x)


class GCN_PairNorm(nn.Module):
    """Zhao & Akoglu 2020: x ← s * (x - mean(x)) / sqrt(<||x_i - mean||^2>)."""
    def __init__(self, in_dim, dim, hidden, depth, k, scale=1.0, eps=1e-6):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim); self.prop = _Propagate(dim, hidden)
        self.head = nn.Linear(dim, k)
        self.depth, self.scale, self.eps = depth, scale, eps
    def _pairnorm(self, x):
        x = x - x.mean(dim=0, keepdim=True)
        rownorm = x.pow(2).sum(dim=-1).mean().sqrt()
        return self.scale * x / (rownorm + self.eps)
    def forward(self, x, Ahat, return_state=False):
        x = self.enc(x)
        for _ in range(self.depth):
            x = self._pairnorm(x + self.prop(x, Ahat))
        return (self.head(x), x) if return_state else self.head(x)


class APPNP(nn.Module):
    """Klicpera et al. 2019: predict-then-propagate with PPR.
    h = MLP(x); for L rounds: h ← (1-α) Ahat h + α h_0."""
    def __init__(self, in_dim, dim, hidden, depth, k, alpha=0.1):
        super().__init__()
        self.mlp = nn.Sequential(
            nn.Linear(in_dim, hidden), nn.GELU(), nn.Linear(hidden, dim)
        )
        self.head = nn.Linear(dim, k); self.depth, self.alpha = depth, alpha
    def forward(self, x, Ahat, return_state=False):
        h0 = self.mlp(x); h = h0
        for _ in range(self.depth):
            h = (1 - self.alpha) * (Ahat @ h) + self.alpha * h0
        return (self.head(h), h) if return_state else self.head(h)


class GCN_GatedRes(nn.Module):
    def __init__(self, in_dim, dim, hidden, depth, k):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim); self.prop = _Propagate(dim, hidden)
        self.gate = nn.Linear(dim, dim); self.head = nn.Linear(dim, k)
        self.depth = depth
    def forward(self, x, Ahat, return_state=False):
        x = self.enc(x)
        for _ in range(self.depth):
            g = torch.sigmoid(self.gate(x))
            x = (1 - g) * x + g * self.prop(x, Ahat)
        return (self.head(x), x) if return_state else self.head(x)


class CPTP_Propagation(nn.Module):
    """Per-node density ρ updated via neighborhood-conditioned Kraus channel."""
    def __init__(self, in_dim, dim, num_kraus, depth, k):
        super().__init__()
        self.d = dim; self.k = num_kraus; self.depth = depth
        self.enc = nn.Linear(in_dim, dim)
        self.raw = nn.Parameter(torch.randn(dim, num_kraus * dim, dim) * 0.5)
        self.head = nn.Linear(dim, k)
    def _kraus(self, context):
        mixed = torch.einsum('nc,cij->nij', context, self.raw)
        Q, _ = torch.linalg.qr(mixed)
        return Q.reshape(-1, self.k, self.d, self.d)
    def forward(self, x, Ahat, return_state=False):
        v = F.normalize(self.enc(x), dim=-1)
        rho = torch.einsum('ni,nj->nij', v, v)
        for _ in range(self.depth):
            diag = torch.diagonal(rho, dim1=-2, dim2=-1)
            context = Ahat @ diag
            K = self._kraus(context)
            K_rho = torch.einsum('nkij,njl->nkil', K, rho)
            new_rho = torch.einsum('nkij,nkjl->nkil',
                                   K_rho, K.transpose(-1, -2))
            rho = new_rho.sum(dim=1)
            rho = 0.5 * (rho + rho.transpose(-1, -2))
        p = torch.diagonal(rho, dim1=-2, dim2=-1)
        return (self.head(p), p) if return_state else self.head(p)


class CPTPReadoutOnly(nn.Module):
    def __init__(self, in_dim, dim, num_kraus, depth, k):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim)
        self.raw = nn.Parameter(torch.randn(dim, num_kraus * dim, dim) * 0.5)
        self.head = nn.Linear(dim, k)
    def forward(self, x, Ahat, return_state=False):
        v = F.normalize(self.enc(x), dim=-1)
        rho = torch.einsum('ni,nj->nij', v, v)
        p = torch.diagonal(rho, dim1=-2, dim2=-1)
        return (self.head(p), p) if return_state else self.head(p)


# ---------------- Diagnostics ----------------

@torch.no_grad()
def diagnose(state, labels):
    """state: (N, d) or (N, K), labels: (N,)"""
    state = state.detach().float()
    # Pairwise cosine similarity
    sn = F.normalize(state, dim=-1)
    C = sn @ sn.T
    n = C.shape[0]
    mean_cos = (C.sum() - C.diag().sum()) / (n * (n - 1))
    # Effective rank: exp(-Σ p_i log p_i) on singular spectrum
    sv = torch.linalg.svdvals(state - state.mean(0, keepdim=True))
    sv = sv / sv.sum().clamp(min=1e-12)
    eff_rank = torch.exp(-(sv * sv.clamp(min=1e-12).log()).sum()).item()
    # Class separation: mean cosine WITHIN class / mean cosine BETWEEN class
    same = labels[:, None] == labels[None, :]
    off = ~torch.eye(n, dtype=torch.bool)
    within = C[same & off].mean().item()
    between = C[~same & off].mean().item()
    return {
        "mean_cos": float(mean_cos),
        "eff_rank": eff_rank,
        "within": within,
        "between": between,
        "separation": within - between,
    }


# ---------------- Training ----------------

def count_params(m): return sum(p.numel() for p in m.parameters())


def train_cora(model, x, Ahat, y, tm, vm, te_mask, labels,
               epochs=300, lr=5e-3, wd=5e-4):
    opt = torch.optim.Adam(model.parameters(), lr=lr, weight_decay=wd)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=epochs)
    best_val = -1.0; best_state = {}
    for _ in range(epochs):
        model.train()
        logits = model(x, Ahat)
        loss = F.cross_entropy(logits[tm], y[tm])
        opt.zero_grad(); loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step(); sched.step()
        with torch.no_grad():
            model.eval()
            logits = model(x, Ahat)
            if not torch.isfinite(logits).all():
                return {"test_acc": 0.0, "diag": None}
            va = (logits[vm].argmax(-1) == y[vm]).float().mean().item()
            if va > best_val:
                best_val = va
                ta = (logits[te_mask].argmax(-1) == y[te_mask]).float().mean().item()
                # Capture state for diagnostics
                _, state = model(x, Ahat, return_state=True)
                # Probabilities for entropy
                probs = F.softmax(logits, dim=-1)
                ent = -(probs * probs.clamp(min=1e-12).log()).sum(-1).mean().item()
                best_state = {
                    "test_acc": ta, "val_acc": best_val, "ent": ent,
                    "diag": diagnose(state, labels),
                }
    return best_state


def main():
    print("Loading Cora...", flush=True)
    x, Ahat, y, tm, vm, te_mask, K = load_cora()
    print(f"Cora: {x.shape[0]} nodes, {K} classes, {x.shape[1]} feats", flush=True)
    print(f"Split: {tm.sum().item()} train / {vm.sum().item()} val / "
          f"{te_mask.sum().item()} test\n", flush=True)

    IN_DIM = x.shape[1]
    DIM = 16
    HIDDEN = 32
    NUM_KRAUS = 4
    DEPTHS = [2, 8, 32]
    SEEDS = [0, 1, 2]

    archs = [
        ("GCN+PreLN",     lambda d: GCN_PreLN(IN_DIM, DIM, HIDDEN, d, K)),
        ("GCN+PairNorm",  lambda d: GCN_PairNorm(IN_DIM, DIM, HIDDEN, d, K)),
        ("APPNP",         lambda d: APPNP(IN_DIM, DIM, HIDDEN, d, K)),
        ("GCN+GatedRes",  lambda d: GCN_GatedRes(IN_DIM, DIM, HIDDEN, d, K)),
        ("CPTP-Prop",     lambda d: CPTP_Propagation(IN_DIM, DIM, NUM_KRAUS, d, K)),
        ("CPTPReadoutOnly", lambda d: CPTPReadoutOnly(IN_DIM, DIM, NUM_KRAUS, d, K)),
    ]
    print("Param counts (depth=8):", flush=True)
    for name, ctor in archs:
        print(f"  {name:20} {count_params(ctor(8)):>6d}", flush=True)
    print(f"\nRandom-chance baseline ({K} classes): {1/K:.3f}\n", flush=True)

    results = {n: {d: [] for d in DEPTHS} for n, _ in archs}
    diagnostics = {n: {d: [] for d in DEPTHS} for n, _ in archs}

    for depth in DEPTHS:
        print(f"=== Depth L = {depth} ===", flush=True)
        for name, ctor in archs:
            for seed in SEEDS:
                torch.manual_seed(seed)
                out = train_cora(ctor(depth), x, Ahat, y, tm, vm, te_mask, y)
                results[name][depth].append(out.get("test_acc", 0.0))
                if out.get("diag") is not None:
                    diagnostics[name][depth].append(out)
            accs = results[name][depth]
            mean = sum(accs) / len(accs)
            std = (sum((a - mean) ** 2 for a in accs) / len(accs)) ** 0.5
            print(f"  {name:20} acc {mean:.3f} ± {std:.3f}  "
                  f"seeds: {[f'{a:.3f}' for a in accs]}", flush=True)
        print(flush=True)

    print("=" * 90, flush=True)
    print("Phase 3 Cora — test accuracy", flush=True)
    print("=" * 90, flush=True)
    print("arch                  " + "  ".join(f"L={d:<13}" for d in DEPTHS), flush=True)
    for name, _ in archs:
        row = f"{name:20}  "
        for d in DEPTHS:
            accs = results[name][d]
            mean = sum(accs) / len(accs)
            std = (sum((a - mean) ** 2 for a in accs) / len(accs)) ** 0.5
            row += f"{mean:.3f}±{std:.3f}    "
        print(row, flush=True)

    print("\n" + "=" * 90, flush=True)
    print("Oversmoothing diagnostics @ best-val checkpoint (mean over 3 seeds)", flush=True)
    print("=" * 90, flush=True)
    print(f"{'arch':<22}{'depth':<8}{'ent':<8}{'cos':<8}{'eff_rk':<10}{'sep':<8}", flush=True)
    for name, _ in archs:
        for d in DEPTHS:
            diags = diagnostics[name][d]
            if not diags: continue
            ent = sum(x["ent"] for x in diags) / len(diags)
            cos = sum(x["diag"]["mean_cos"] for x in diags) / len(diags)
            er = sum(x["diag"]["eff_rank"] for x in diags) / len(diags)
            sep = sum(x["diag"]["separation"] for x in diags) / len(diags)
            print(f"{name:<22}{d:<8}{ent:<8.3f}{cos:<8.3f}{er:<10.2f}{sep:<8.3f}",
                  flush=True)


if __name__ == "__main__":
    main()
