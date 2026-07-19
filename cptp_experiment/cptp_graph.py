"""
CPTP residual block — Phase 3: real task with simplex-valued state.

Task: node classification on Stochastic Block Model graphs by iterative
label propagation. K-class community detection. Each node maintains a
distribution (or density matrix) over K classes; classification is the
argmax of the final distribution.

Iteration = message-passing rounds. The well-documented failure mode of
deep GNN-style propagation is OVERSMOOTHING — at large depth, all nodes'
representations converge to the same value and class information is lost.
This is precisely the rank-collapse phenomenon CPTP residual blocks
prevent on synthetic data (Phase 2). Phase 3 tests whether the advantage
transfers to a real iterative refinement task.

Architectures:
  (A) GCN+PreLN       y ← LN(y + propagate(y, W))
  (B) GCN+RMSNorm     y ← RMSNorm(y + propagate(y, W))
  (C) GCN+ReZero      y ← y + γ * propagate(y, W), γ init 0
  (D) GCN+GatedRes    y ← (1-σ(g))*y + σ(g)*propagate(y, W)
  (E) CPTP-Prop       per-node ρ updated via observation-conditioned Kraus

Architecture (E) is the natural CPTP analog of label propagation:
the per-node density matrix evolves via a CPTP channel whose Kraus
operators depend on the aggregated neighborhood. Trace preservation
means each node ALWAYS holds a valid probability distribution.
"""

import math
import torch
import torch.nn as nn
import torch.nn.functional as F


# ---------------- SBM graph generation ----------------

def sample_sbm(n_per_class=50, k=4, p_in=0.30, p_out=0.05, seed=0):
    """Stochastic Block Model: k communities of n_per_class nodes each.
    Returns: edge_index (2, E), labels (N,), normalized adjacency Ahat (N, N)."""
    g = torch.Generator().manual_seed(seed)
    n = n_per_class * k
    labels = torch.arange(k).repeat_interleave(n_per_class)
    # Edge probabilities by class match
    prob_mat = torch.where(labels[:, None] == labels[None, :], p_in, p_out)
    rand = torch.rand(n, n, generator=g)
    adj = (rand < prob_mat).float()
    adj = torch.triu(adj, diagonal=1)
    adj = adj + adj.T  # symmetric
    adj.fill_diagonal_(1)  # self-loops
    deg = adj.sum(dim=1)
    d_inv_sqrt = deg.pow(-0.5)
    Ahat = adj * d_inv_sqrt[:, None] * d_inv_sqrt[None, :]
    return Ahat, labels


def make_features(labels, k, d=16, noise=1.0, seed=0):
    """Each class has a fixed random prototype; node features = prototype + noise."""
    g = torch.Generator().manual_seed(seed)
    protos = torch.randn(k, d, generator=g)
    protos = F.normalize(protos, dim=-1) * 3.0
    x = protos[labels] + noise * torch.randn(len(labels), d, generator=g)
    return x


# ---------------- Architectures ----------------

class _Propagate(nn.Module):
    """One round of label-propagation-style message passing: x ← Ahat @ x @ W."""
    def __init__(self, dim, hidden):
        super().__init__()
        self.W = nn.Linear(dim, hidden); self.U = nn.Linear(hidden, dim)
    def forward(self, x, Ahat):
        return self.U(F.gelu(self.W(Ahat @ x)))


class GCN_PreLN(nn.Module):
    def __init__(self, in_dim, dim, hidden, depth, k):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim); self.ln = nn.LayerNorm(dim)
        self.prop = _Propagate(dim, hidden); self.head = nn.Linear(dim, k)
        self.depth = depth
    def forward(self, x, Ahat):
        x = self.enc(x)
        for _ in range(self.depth): x = self.ln(x + self.prop(x, Ahat))
        return self.head(x)


class GCN_RMSNorm(nn.Module):
    def __init__(self, in_dim, dim, hidden, depth, k, eps=1e-6):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim); self.prop = _Propagate(dim, hidden)
        self.gain = nn.Parameter(torch.ones(dim)); self.head = nn.Linear(dim, k)
        self.depth, self.eps = depth, eps
    def forward(self, x, Ahat):
        x = self.enc(x)
        for _ in range(self.depth):
            x = x + self.prop(x, Ahat)
            rms = x.pow(2).mean(-1, keepdim=True).add(self.eps).sqrt()
            x = self.gain * x / rms
        return self.head(x)


class GCN_ReZero(nn.Module):
    def __init__(self, in_dim, dim, hidden, depth, k):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim); self.prop = _Propagate(dim, hidden)
        self.gamma = nn.Parameter(torch.zeros(1)); self.head = nn.Linear(dim, k)
        self.depth = depth
    def forward(self, x, Ahat):
        x = self.enc(x)
        for _ in range(self.depth): x = x + self.gamma * self.prop(x, Ahat)
        return self.head(x)


class GCN_GatedRes(nn.Module):
    def __init__(self, in_dim, dim, hidden, depth, k):
        super().__init__()
        self.enc = nn.Linear(in_dim, dim); self.prop = _Propagate(dim, hidden)
        self.gate = nn.Linear(dim, dim); self.head = nn.Linear(dim, k)
        self.depth = depth
    def forward(self, x, Ahat):
        x = self.enc(x)
        for _ in range(self.depth):
            g = torch.sigmoid(self.gate(x))
            x = (1 - g) * x + g * self.prop(x, Ahat)
        return self.head(x)


class CPTP_Propagation(nn.Module):
    """
    CPTP-style label propagation.

    Each node holds a (real, symmetric, PSD, trace-1) density matrix
    ρ_v ∈ R^{d×d}. At each round, build neighborhood-aggregated context
    c_v = Σ_u Ahat[v,u] · diag(ρ_u) ∈ R^d, build context-dependent Kraus
    operators K_i(c_v), apply
        ρ_v ← Σ_i K_i(c_v) ρ_v K_i(c_v)^T,
    and read posterior as diag(ρ_v).

    Σ K_i^T K_i = I enforced via thin QR on the stacked Kraus tensor.
    Trace preservation is architectural; no normalization needed.
    """
    def __init__(self, in_dim, dim, num_kraus, depth, k):
        super().__init__()
        self.d = dim; self.k = num_kraus; self.depth = depth
        self.enc = nn.Linear(in_dim, dim)
        # Per-context-channel Kraus parametrization: raw[c, :, :] for context dim c
        self.raw = nn.Parameter(torch.randn(dim, num_kraus * dim, dim) * 0.5)
        self.head = nn.Linear(dim, k)

    def _kraus(self, context):
        # context: (N, d) — per-node context vector
        # raw : (d, k*d, d)  → mix: (N, k*d, d) = Σ_c context[N,c] * raw[c, :, :]
        mixed = torch.einsum('nc,cij->nij', context, self.raw)
        Q, _ = torch.linalg.qr(mixed)
        return Q.reshape(-1, self.k, self.d, self.d)

    def forward(self, x, Ahat):
        v = F.normalize(self.enc(x), dim=-1)
        rho = torch.einsum('ni,nj->nij', v, v)  # (N, d, d)
        for _ in range(self.depth):
            diag = torch.diagonal(rho, dim1=-2, dim2=-1)  # (N, d)
            context = Ahat @ diag                          # (N, d)
            K = self._kraus(context)                       # (N, k, d, d)
            K_rho = torch.einsum('nkij,njl->nkil', K, rho)
            new_rho = torch.einsum('nkij,nkjl->nkil',
                                   K_rho, K.transpose(-1, -2))
            rho = new_rho.sum(dim=1)
            rho = 0.5 * (rho + rho.transpose(-1, -2))
        p = torch.diagonal(rho, dim1=-2, dim2=-1)
        return self.head(p)


# ---------------- Training ----------------

def count_params(m): return sum(p.numel() for p in m.parameters())


def train_node_classifier(model, x, Ahat, y, train_mask, val_mask,
                          epochs=300, lr=3e-3):
    opt = torch.optim.Adam(model.parameters(), lr=lr, weight_decay=5e-4)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=epochs)
    best_val_acc = 0.0
    for _ in range(epochs):
        model.train()
        logits = model(x, Ahat)
        loss = F.cross_entropy(logits[train_mask], y[train_mask])
        opt.zero_grad(); loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step(); sched.step()
        with torch.no_grad():
            model.eval()
            logits = model(x, Ahat)
            if not torch.isfinite(logits).all():
                return 0.0
            val_acc = (logits[val_mask].argmax(-1) == y[val_mask]).float().mean().item()
            best_val_acc = max(best_val_acc, val_acc)
    return best_val_acc


def main():
    K = 4              # n_classes / communities
    N_PER = 50         # nodes per class — total N = 200
    IN_DIM = 16
    DIM = 16
    HIDDEN = 32
    NUM_KRAUS = 4
    DEPTHS = [2, 8, 32]
    SEEDS = [0, 1, 2]
    P_IN, P_OUT = 0.30, 0.05    # community structure: in/out edge prob
    NOISE = 1.5                  # feature noise — node features alone insufficient

    archs = [
        ("GCN+PreLN",     lambda d: GCN_PreLN(IN_DIM, DIM, HIDDEN, d, K)),
        ("GCN+RMSNorm",   lambda d: GCN_RMSNorm(IN_DIM, DIM, HIDDEN, d, K)),
        ("GCN+ReZero",    lambda d: GCN_ReZero(IN_DIM, DIM, HIDDEN, d, K)),
        ("GCN+GatedRes",  lambda d: GCN_GatedRes(IN_DIM, DIM, HIDDEN, d, K)),
        ("CPTP-Prop",     lambda d: CPTP_Propagation(IN_DIM, DIM, NUM_KRAUS, d, K)),
    ]

    print(f"SBM graph: {N_PER*K} nodes, {K} classes, p_in={P_IN}, p_out={P_OUT}")
    print(f"Features: dim {IN_DIM}, noise {NOISE} (high — graph signal required)")
    print("\nParam counts (depth=8):", flush=True)
    for name, ctor in archs:
        print(f"  {name:18} {count_params(ctor(8)):>5d}", flush=True)
    print(f"\nRandom-chance baseline ({K} classes): {1/K:.3f}\n", flush=True)

    results = {n: [] for n, _ in archs}

    for depth in DEPTHS:
        print(f"=== Depth L = {depth} ===", flush=True)
        for name, ctor in archs:
            accs = []
            for seed in SEEDS:
                torch.manual_seed(seed)
                Ahat, y = sample_sbm(N_PER, K, P_IN, P_OUT, seed=seed)
                x = make_features(y, K, IN_DIM, NOISE, seed=seed + 100)
                n = len(y); perm = torch.randperm(n, generator=torch.Generator().manual_seed(seed+200))
                train_mask = torch.zeros(n, dtype=torch.bool); train_mask[perm[:n//5]] = True
                val_mask = torch.zeros(n, dtype=torch.bool); val_mask[perm[n//5:]] = True
                model = ctor(depth)
                acc = train_node_classifier(model, x, Ahat, y, train_mask, val_mask)
                accs.append(acc)
            mean = sum(accs)/len(accs)
            std = (sum((a-mean)**2 for a in accs)/len(accs))**0.5
            results[name].append((depth, mean, std))
            mark = "**" if mean > 0.5 else ("* " if mean > 1/K + 0.1 else "  ")
            print(f"  {mark} {name:18} {mean:.3f} ± {std:.3f}   "
                  f"seeds: {[f'{a:.3f}' for a in accs]}", flush=True)
        print(flush=True)

    print("=" * 78, flush=True)
    print("Phase 3 summary — best val accuracy (mean ± std, 3 seeds)", flush=True)
    print(f"** > 0.5,  * > 0.35 (random+0.10),  blank = random-like", flush=True)
    print("=" * 78, flush=True)
    print("arch              " + "  ".join(f"L={d:<13}" for d in DEPTHS), flush=True)
    for name in [n for n, _ in archs]:
        row = f"{name:18}"
        for _, mean, std in results[name]:
            mk = "**" if mean > 0.5 else ("* " if mean > 1/K + 0.10 else "  ")
            row += f"{mean:.3f}±{std:.3f}{mk}   "
        print(row, flush=True)


if __name__ == "__main__":
    main()
