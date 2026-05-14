"""
EXPERIMENT A v2: Test Volterra-SV regularizer on tasks that SHOULD benefit.

Tasks tested:
  (1) COPY: y_t = u_{t-delay}   — needs SPARSE impulse, doesn't suit Volterra
  (2) INTEGRATION: y_t = Σ_{s≤t} u_s   — IS the Volterra operator (ideal target)
  (3) SMOOTHING: y_t = (1/W) Σ_{s=t-W..t} u_s  — moving average (smooth kernel)
  (4) DECAY: y_t = Σ_{s≤t} u_s · exp(-(t-s)/τ)  — exponential-weighted (smooth)

Multi-seed averaging to filter noise.
"""
import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np

torch.manual_seed(42)
np.random.seed(42)


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
        K = h[safe_offset] * mask.float()
        return K


def volterra_regularizer(K, n_modes=8):
    U, S, Vh = torch.linalg.svd(K)
    if S[0].item() < 1e-8:
        return torch.tensor(0.0, device=K.device)
    S_normalized = S[:n_modes] / S[0]
    target = torch.tensor([1.0/(2*k-1) for k in range(1, n_modes+1)],
                          dtype=K.dtype, device=K.device)
    return ((S_normalized - target) ** 2).sum()


# ─────────────────────────────────────────────────────────────────
# Tasks
# ─────────────────────────────────────────────────────────────────

def make_copy(batch=32, L=32, delay=8):
    u = torch.randint(0, 2, (batch, L, 1), dtype=torch.float32) * 2 - 1
    y = torch.zeros_like(u)
    y[:, delay:, :] = u[:, :L-delay, :]
    return u, y


def make_integration(batch=32, L=32):
    """y_t = Σ_{s ≤ t} u_s — exactly the Volterra operator."""
    u = torch.randn(batch, L, 1) * 0.3
    y = torch.cumsum(u, dim=1)
    return u, y


def make_smoothing(batch=32, L=32, W=8):
    """y_t = (1/W) Σ_{s=t-W+1..t} u_s — moving average."""
    u = torch.randn(batch, L, 1) * 0.5
    # Apply rectangular smoothing
    kernel = torch.ones(1, 1, W) / W
    u_padded = F.pad(u.transpose(1, 2), (W-1, 0))  # left-pad
    y = F.conv1d(u_padded, kernel).transpose(1, 2)
    return u, y


def make_decay(batch=32, L=32, tau=4.0):
    """y_t = Σ_{s ≤ t} u_s · exp(-(t-s)/τ) — exponential-weighted causal sum."""
    u = torch.randn(batch, L, 1) * 0.5
    # Build exp-decay kernel
    times = torch.arange(L, dtype=torch.float32)
    kernel = torch.exp(-times/tau).flip(0).reshape(1, 1, L)
    u_padded = F.pad(u.transpose(1, 2), (L-1, 0))
    y = F.conv1d(u_padded, kernel).transpose(1, 2)
    return u, y


TASKS = {
    'copy': lambda: make_copy(L=32, delay=8),
    'integration': lambda: make_integration(L=32),
    'smoothing': lambda: make_smoothing(L=32, W=8),
    'decay': lambda: make_decay(L=32, tau=4.0),
}


# ─────────────────────────────────────────────────────────────────
# Training
# ─────────────────────────────────────────────────────────────────

def train_one(task_fn, lambda_reg=0.0, n_steps=600, lr=3e-3, L=32, n_modes=8, seed=42):
    torch.manual_seed(seed)
    model = TinySSM(state_dim=16)
    opt = torch.optim.Adam(model.parameters(), lr=lr)

    for step in range(n_steps):
        u, y = task_fn()
        y_pred = model(u)
        task_loss = F.mse_loss(y_pred, y)

        if lambda_reg > 0:
            K = model.impulse_kernel(L)
            reg_loss = volterra_regularizer(K, n_modes=n_modes)
            loss = task_loss + lambda_reg * reg_loss
        else:
            loss = task_loss

        opt.zero_grad()
        loss.backward()
        opt.step()

    # Final evaluation
    model.eval()
    eval_losses = []
    with torch.no_grad():
        for _ in range(20):
            u, y = task_fn()
            y_pred = model(u)
            eval_losses.append(F.mse_loss(y_pred, y).item())
    return float(np.mean(eval_losses)), model


# ─────────────────────────────────────────────────────────────────
# Run all tasks × all regularizer strengths × multiple seeds
# ─────────────────────────────────────────────────────────────────

print("="*72)
print("EXPERIMENT A v2: VOLTERRA REGULARIZER ACROSS TASKS")
print("="*72)

LAMBDAS = [0.0, 0.01, 0.1, 1.0]
SEEDS = [42, 43, 44]
N_STEPS = 500

results = {}
for task_name, task_fn in TASKS.items():
    print(f"\n--- Task: {task_name} ---")
    results[task_name] = {}
    for lam in LAMBDAS:
        seed_losses = []
        for seed in SEEDS:
            loss, _ = train_one(task_fn, lambda_reg=lam, n_steps=N_STEPS, seed=seed)
            seed_losses.append(loss)
        mean_loss = float(np.mean(seed_losses))
        std_loss = float(np.std(seed_losses))
        results[task_name][lam] = (mean_loss, std_loss)
        print(f"  λ={lam:6.2f}: mean_loss = {mean_loss:.5f} ± {std_loss:.5f}  (3 seeds)")

print("\n" + "="*72)
print("SUMMARY TABLE")
print("="*72)

print(f"\n{'Task':<15} | {'Baseline (λ=0)':>15} | {'Best regularized':>18} | {'Best λ':>8} | {'Improvement':>12}")
print("-"*100)

for task_name in TASKS:
    base_mean, base_std = results[task_name][0.0]
    # Find best non-zero λ
    best_lam = None
    best_loss = float('inf')
    for lam in LAMBDAS[1:]:
        m, _ = results[task_name][lam]
        if m < best_loss:
            best_loss = m
            best_lam = lam
    improvement = (base_mean - best_loss) / base_mean * 100 if base_mean > 0 else 0
    sign = "✓" if improvement > 0 else "✗"
    print(f"{task_name:<15} | {base_mean:9.5f} ±{base_std:.4f} | {best_loss:13.5f} (λ={best_lam}) | {best_lam:>8.2f} | {improvement:+11.2f}% {sign}")

print("\n" + "="*72)
print("INTERPRETATION")
print("="*72)

print("""
EXPECTED a priori:
  • copy: regularizer should HURT (sparse impulse needed, not smooth)
  • integration: regularizer should HELP STRONGLY (Volterra IS integration)
  • smoothing: regularizer should HELP MODESTLY (smooth kernel target)
  • decay: regularizer should HELP MODESTLY (smooth, decaying kernel)

If integration shows large improvement: Volterra target is RIGHT for integration-like tasks.
If smoothing/decay show moderate improvement: target generalizes to smooth-kernel tasks.
If copy gets worse: confirms task-dependence (regularizer not universally good).
""")

# Strong winners
strong_wins = []
weak_wins = []
losses = []
for task_name in TASKS:
    base_mean, _ = results[task_name][0.0]
    best_loss = min(results[task_name][lam][0] for lam in LAMBDAS[1:])
    improvement = (base_mean - best_loss) / base_mean * 100 if base_mean > 0 else 0
    if improvement > 10:
        strong_wins.append((task_name, improvement))
    elif improvement > 1:
        weak_wins.append((task_name, improvement))
    elif improvement < -1:
        losses.append((task_name, improvement))

print(f"STRONG WINS (>10% improvement): {strong_wins}")
print(f"WEAK WINS (1-10% improvement):  {weak_wins}")
print(f"LOSSES (regularizer hurt >1%):  {losses}")

if strong_wins:
    print("\n✓✓ Volterra regularizer MEANINGFULLY IMPROVES at least one task.")
    print("    Pursue further with larger models / standard SSM benchmarks.")
elif weak_wins and not losses:
    print("\n✓ Volterra regularizer marginally helps without hurting. Worth further testing.")
elif losses and not strong_wins:
    print("\n✗ Volterra regularizer hurts more than it helps. Wrong target for these tasks.")
else:
    print("\n? Mixed results. Task-dependent.")
