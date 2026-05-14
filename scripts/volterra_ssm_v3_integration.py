"""
EXPERIMENT A v3: Confirm integration-task win with more seeds + longer training.

The v2 result: Volterra regularizer gives +6.6% on integration (3 seeds).
Std was high (±0.21). This script: 8 seeds, longer training, sweep λ finely.
"""
import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np


class TinySSM(nn.Module):
    def __init__(self, state_dim=16, init_scale=0.1):
        super().__init__()
        A_init = torch.eye(state_dim) * 0.9 + init_scale * torch.randn(state_dim, state_dim)
        self.A = nn.Parameter(A_init)
        self.B = nn.Parameter(init_scale * torch.randn(state_dim, 1))
        self.C = nn.Parameter(init_scale * torch.randn(1, state_dim))

    def forward(self, u):
        batch, L, _ = u.shape
        x = torch.zeros(batch, self.A.shape[0], device=u.device)
        ys = []
        for t in range(L):
            x = x @ self.A.T + u[:, t, :] @ self.B.T
            y = x @ self.C.T
            ys.append(y)
        return torch.stack(ys, dim=1)

    def impulse_kernel(self, L):
        H = self.A.shape[0]
        h = []
        Ak = torch.eye(H, device=self.A.device, dtype=self.A.dtype)
        for k in range(L):
            val = (self.C @ Ak @ self.B).squeeze()
            h.append(val)
            Ak = Ak @ self.A
        h = torch.stack(h)
        idx_i = torch.arange(L).unsqueeze(1).expand(L, L)
        idx_j = torch.arange(L).unsqueeze(0).expand(L, L)
        offset = idx_i - idx_j
        mask = offset >= 0
        safe_offset = offset.clamp(min=0)
        return h[safe_offset] * mask.float()


def volterra_reg(K, n_modes=8):
    S = torch.linalg.svdvals(K)
    if S[0].item() < 1e-8: return torch.tensor(0.0, device=K.device)
    Sn = S[:n_modes] / S[0]
    target = torch.tensor([1.0/(2*k-1) for k in range(1, n_modes+1)],
                          dtype=K.dtype, device=K.device)
    return ((Sn - target) ** 2).sum()


def make_integration(batch=32, L=32):
    u = torch.randn(batch, L, 1) * 0.3
    y = torch.cumsum(u, dim=1)
    return u, y


def train_integration(lambda_reg=0.0, n_steps=1000, lr=3e-3, L=32, n_modes=8, seed=42):
    torch.manual_seed(seed)
    np.random.seed(seed)
    model = TinySSM(state_dim=16)
    opt = torch.optim.Adam(model.parameters(), lr=lr)

    for step in range(n_steps):
        u, y = make_integration(L=L)
        y_pred = model(u)
        task_loss = F.mse_loss(y_pred, y)

        if lambda_reg > 0:
            K = model.impulse_kernel(L)
            loss = task_loss + lambda_reg * volterra_reg(K, n_modes=n_modes)
        else:
            loss = task_loss

        opt.zero_grad()
        loss.backward()
        opt.step()

    # Eval
    model.eval()
    eval_losses = []
    with torch.no_grad():
        for _ in range(40):
            u, y = make_integration(L=L)
            y_pred = model(u)
            eval_losses.append(F.mse_loss(y_pred, y).item())
    return float(np.mean(eval_losses))


print("="*72)
print("EXPERIMENT A v3: INTEGRATION TASK — confirming the +6.6% win")
print("="*72)
print("\nConfig: 8 seeds × 1000 steps × λ ∈ {0, 0.1, 0.3, 1.0, 3.0}")
print("        Hypothesis: Volterra regularizer should help integration task")
print("        (since Volterra operator IS the integration kernel)")

LAMBDAS = [0.0, 0.1, 0.3, 1.0, 3.0]
SEEDS = list(range(8))

results = {}
for lam in LAMBDAS:
    seed_losses = []
    for seed in SEEDS:
        loss = train_integration(lambda_reg=lam, n_steps=1000, seed=seed)
        seed_losses.append(loss)
    mean_l = np.mean(seed_losses)
    std_l = np.std(seed_losses)
    sem_l = std_l / np.sqrt(len(SEEDS))
    results[lam] = (mean_l, std_l, sem_l, seed_losses)
    print(f"  λ={lam:5.2f}: mean = {mean_l:.5f} ± {sem_l:.5f} (SEM)  "
          f"std={std_l:.5f}  seeds={[f'{l:.3f}' for l in seed_losses]}")

print("\n" + "="*72)
print("STATISTICAL ANALYSIS")
print("="*72)

base_mean, base_std, base_sem, base_losses = results[0.0]
print(f"\nBaseline (λ=0):  {base_mean:.5f} ± {base_sem:.5f} (SEM, n=8)")
print()

# Find best λ
best_lam = 0.0
best_mean = base_mean
for lam in LAMBDAS[1:]:
    m, _, _, _ = results[lam]
    if m < best_mean:
        best_mean = m
        best_lam = lam

best_data = results[best_lam]
print(f"Best regularizer: λ={best_lam}, mean = {best_data[0]:.5f} ± {best_data[2]:.5f} (SEM)")
print(f"Improvement: {(base_mean - best_data[0])/base_mean*100:+.2f}%")

# Paired t-test (sort of) — same seeds for baseline and best λ
import scipy.stats as stats
diffs = [b - r for b, r in zip(base_losses, best_data[3])]
t_stat, p_value = stats.ttest_rel(base_losses, best_data[3])
mean_diff = np.mean(diffs)
print(f"\nPaired comparison baseline vs best λ:")
print(f"  Mean diff (baseline - best): {mean_diff:.5f}")
print(f"  Diffs across seeds: {[f'{d:+.4f}' for d in diffs]}")
print(f"  Number of seeds where reg WINS: {sum(1 for d in diffs if d > 0)}/{len(diffs)}")
print(f"  t-statistic: {t_stat:.3f}, p-value: {p_value:.4f}")

if p_value < 0.05 and mean_diff > 0:
    print("\n✓✓ STATISTICALLY SIGNIFICANT improvement (p < 0.05).")
elif p_value < 0.10 and mean_diff > 0:
    print("\n✓ MARGINALLY SIGNIFICANT improvement (p < 0.10).")
elif mean_diff > 0:
    print("\n? Improvement direction CORRECT but not statistically significant.")
else:
    print("\n✗ NO improvement OR wrong direction.")

print("\n" + "="*72)
print("VERDICT")
print("="*72)

if p_value < 0.05 and mean_diff > 0:
    pct = (base_mean - best_data[0])/base_mean*100
    print(f"""
✓ CONFIRMED: Volterra regularizer significantly improves integration task by {pct:.1f}%
  with p = {p_value:.4f} (paired t-test, n=8 seeds).

This is a real, statistically supported result:
  • Volterra σ_k = 2/((2k-1)π) IS the singular value spectrum of the
    continuous integration operator
  • Pushing the SSM kernel SVs toward this target genuinely helps the
    model learn integration
  • The same regularizer hurts copy and smoothing tasks (different kernel shapes)

Next steps:
  • Test on standard SSM benchmarks (Long Range Arena, sequential MNIST)
  • Compare to HiPPO initialization (which already targets specific
    polynomials — does Volterra add value beyond HiPPO?)
  • Test on JEPA-style energy losses with state-space backbone
""")
elif mean_diff > 0:
    print(f"""
~ TENTATIVE: Improvement direction is right but signal weak.
  Mean improvement: {(base_mean - best_data[0])/base_mean*100:.2f}%
  But p = {p_value:.4f} ≥ 0.05, so we can't rule out noise.

  Need more seeds, or task variant where the effect is stronger.
""")
else:
    print(f"""
✗ NOT CONFIRMED: regularizer doesn't help integration task in this config.

  The earlier 6.6% might have been seed luck. The fundamental issue may
  be that the Volterra continuous SV pattern doesn't perfectly match the
  discrete-time integration kernel for finite L.
""")
