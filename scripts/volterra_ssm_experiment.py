"""
EXPERIMENT A: Volterra-SV regularizer for state-space models.

Setup:
  Tiny SSM: state dim H, sequence length L
  ẋ_t = A x_{t-1} + B u_t,  y_t = C x_t

  Convolution kernel: K_{ij} = C A^{i-j} B for j <= i (lower triangular)
  SVs of K compared to Volterra target σ_k = 2/((2k-1)π).

Tasks:
  Copy task: u is a random sequence; y_t should equal u_{t-delay}.
  Memory benchmark — discriminates "good" causal-attention from "collapsed".

Compare:
  Baseline: standard SSM loss
  Regularized: + λ · ||SV(K) - σ_target||²
"""
import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import math

torch.manual_seed(42)
np.random.seed(42)

# ─────────────────────────────────────────────────────────────────
# 1. SSM module
# ─────────────────────────────────────────────────────────────────

class TinySSM(nn.Module):
    """Minimal causal SSM: x_t = A x_{t-1} + B u_t, y_t = C x_t.

    State dim H, input dim 1, output dim 1 (for the copy task).
    """
    def __init__(self, state_dim=16, init_scale=0.1):
        super().__init__()
        # Initialize A close to stable (eigenvalues |λ| < 1)
        A_init = torch.eye(state_dim) * 0.9 + init_scale * torch.randn(state_dim, state_dim)
        self.A = nn.Parameter(A_init)
        self.B = nn.Parameter(init_scale * torch.randn(state_dim, 1))
        self.C = nn.Parameter(init_scale * torch.randn(1, state_dim))

    def forward(self, u):
        """u: (batch, L, 1) → y: (batch, L, 1)."""
        batch, L, _ = u.shape
        x = torch.zeros(batch, self.A.shape[0], device=u.device)
        ys = []
        for t in range(L):
            x = x @ self.A.T + u[:, t, :] @ self.B.T
            y = x @ self.C.T
            ys.append(y)
        return torch.stack(ys, dim=1)

    def impulse_kernel(self, L):
        """Compute the L×L convolution kernel K[i,j] = C @ A^(i-j) @ B for j ≤ i.

        Returns a tensor with gradient flow preserved.
        """
        H = self.A.shape[0]
        # Compute h_k = C @ A^k @ B for k = 0, 1, ..., L-1 (a length-L tensor)
        h = []
        Ak = torch.eye(H, device=self.A.device, dtype=self.A.dtype)
        for k in range(L):
            val = (self.C @ Ak @ self.B).squeeze()  # scalar tensor (keeps grad)
            h.append(val)
            Ak = Ak @ self.A
        h = torch.stack(h)  # (L,)
        # Build lower-triangular Toeplitz matrix from h: K[i, j] = h[i - j] for j ≤ i
        # Use indexing trick for grad-friendly construction
        idx_i = torch.arange(L).unsqueeze(1).expand(L, L)
        idx_j = torch.arange(L).unsqueeze(0).expand(L, L)
        offset = idx_i - idx_j  # (L, L), values in [-L+1, L-1]
        mask = offset >= 0  # only fill lower triangle (causal)
        # Gather h values at valid offsets
        safe_offset = offset.clamp(min=0)  # avoid neg index for masked entries
        K = h[safe_offset] * mask.float()
        return K


# ─────────────────────────────────────────────────────────────────
# 2. Volterra SV target and regularizer
# ─────────────────────────────────────────────────────────────────

def volterra_sv_target(L, K_subset=None):
    """Volterra σ_k = 2/((2k-1)π), normalized appropriately.

    For comparison with discrete kernel SVs at length L, we need to scale.
    The continuous Volterra has σ_1 = 2/π ≈ 0.637.
    Discrete L×L lower-triangular ones matrix has σ_1 ≈ 2L/π (scales linearly with L).

    For our purposes: just take the RATIO sequence σ_k/σ_1 = 1/(2k-1) and
    scale by the actual σ_1 of the trained kernel.
    """
    k = torch.arange(1, L+1, dtype=torch.float32)
    return 1.0 / (2.0 * k - 1.0)  # ratios σ_k/σ_1 = 1/(2k-1)


def volterra_regularizer(K, n_modes=8):
    """Compute λ · ||SV(K)/σ_1(K) - target||² over top n_modes."""
    # SVD of K
    U, S, Vh = torch.linalg.svd(K)
    # Normalize by σ_1
    if S[0].item() < 1e-8:
        return torch.tensor(0.0, device=K.device)
    S_normalized = S[:n_modes] / S[0]
    # Target is 1/(2k-1)
    target = volterra_sv_target(n_modes).to(K.device)
    return ((S_normalized - target) ** 2).sum()


# ─────────────────────────────────────────────────────────────────
# 3. Copy task
# ─────────────────────────────────────────────────────────────────

def make_copy_batch(batch=32, L=32, delay=8):
    """Random binary input; target = input shifted by `delay` (pad zeros at start)."""
    u = torch.randint(0, 2, (batch, L, 1), dtype=torch.float32) * 2 - 1  # ±1
    # Target: y_t = u_{t-delay} for t >= delay, else 0
    y = torch.zeros_like(u)
    y[:, delay:, :] = u[:, :L-delay, :]
    return u, y


# ─────────────────────────────────────────────────────────────────
# 4. Training loop
# ─────────────────────────────────────────────────────────────────

def train(model, lambda_reg=0.0, n_steps=400, lr=3e-3, L=32, delay=8, n_modes=8, label="", verbose=True):
    opt = torch.optim.Adam(model.parameters(), lr=lr)
    losses = []
    reg_losses = []

    for step in range(n_steps):
        u, y = make_copy_batch(batch=32, L=L, delay=delay)
        y_pred = model(u)
        task_loss = F.mse_loss(y_pred, y)

        if lambda_reg > 0:
            K = model.impulse_kernel(L)
            reg_loss = volterra_regularizer(K, n_modes=n_modes)
            loss = task_loss + lambda_reg * reg_loss
        else:
            reg_loss = torch.tensor(0.0)
            loss = task_loss

        opt.zero_grad()
        loss.backward()
        opt.step()

        losses.append(task_loss.item())
        reg_losses.append(reg_loss.item())

        if verbose and (step+1) % 50 == 0:
            print(f"  [{label}] step {step+1:4d}: task_loss = {task_loss.item():.4f}, "
                  f"reg_loss = {reg_loss.item():.4f}")

    return losses, reg_losses


# ─────────────────────────────────────────────────────────────────
# 5. Run experiment
# ─────────────────────────────────────────────────────────────────

def evaluate_model(model, n_samples=20, L=32, delay=8):
    """Evaluate task loss on fresh samples."""
    model.eval()
    losses = []
    with torch.no_grad():
        for _ in range(n_samples):
            u, y = make_copy_batch(batch=32, L=L, delay=delay)
            y_pred = model(u)
            losses.append(F.mse_loss(y_pred, y).item())
    model.train()
    return float(np.mean(losses))


def get_sv_pattern(model, L=32, n_modes=8):
    """Return SV pattern of impulse kernel."""
    with torch.no_grad():
        K = model.impulse_kernel(L)
        S = torch.linalg.svdvals(K)
        return S[:n_modes].numpy(), K.numpy()


print("="*72)
print("EXPERIMENT A: VOLTERRA-SV REGULARIZER FOR STATE-SPACE MODELS")
print("="*72)

L = 32
delay = 8
state_dim = 16
n_modes = 8

print(f"\nConfig: state_dim={state_dim}, sequence length L={L}, copy delay={delay}")
print(f"        regularizer over top {n_modes} singular values")
print(f"        Volterra target: σ_k/σ_1 = 1/(2k-1) = {[round(1/(2*k-1), 4) for k in range(1, n_modes+1)]}")

# Run baselines and regularized variants
print("\n--- Training baseline (no regularizer) ---")
torch.manual_seed(42)
model_baseline = TinySSM(state_dim=state_dim)
losses_b, _ = train(model_baseline, lambda_reg=0.0, n_steps=600, label="baseline")
final_b = evaluate_model(model_baseline, L=L, delay=delay)
sv_b, K_b = get_sv_pattern(model_baseline, L=L, n_modes=n_modes)

print("\n--- Training with Volterra regularizer (λ = 0.01) ---")
torch.manual_seed(42)
model_reg_small = TinySSM(state_dim=state_dim)
losses_r1, regs_r1 = train(model_reg_small, lambda_reg=0.01, n_steps=600, n_modes=n_modes, label="λ=0.01")
final_r1 = evaluate_model(model_reg_small, L=L, delay=delay)
sv_r1, K_r1 = get_sv_pattern(model_reg_small, L=L, n_modes=n_modes)

print("\n--- Training with Volterra regularizer (λ = 0.1) ---")
torch.manual_seed(42)
model_reg_med = TinySSM(state_dim=state_dim)
losses_r2, regs_r2 = train(model_reg_med, lambda_reg=0.1, n_steps=600, n_modes=n_modes, label="λ=0.1")
final_r2 = evaluate_model(model_reg_med, L=L, delay=delay)
sv_r2, K_r2 = get_sv_pattern(model_reg_med, L=L, n_modes=n_modes)

print("\n--- Training with Volterra regularizer (λ = 1.0) ---")
torch.manual_seed(42)
model_reg_high = TinySSM(state_dim=state_dim)
losses_r3, regs_r3 = train(model_reg_high, lambda_reg=1.0, n_steps=600, n_modes=n_modes, label="λ=1.0")
final_r3 = evaluate_model(model_reg_high, L=L, delay=delay)
sv_r3, K_r3 = get_sv_pattern(model_reg_high, L=L, n_modes=n_modes)

print("\n" + "="*72)
print("FINAL EVALUATION")
print("="*72)
print(f"\n{'Variant':<25} | {'Final task MSE':>15} | {'Final reg':>12}")
print("-"*60)
print(f"{'Baseline (λ=0)':<25} | {final_b:15.6f} | {'N/A':>12}")
print(f"{'Volterra reg (λ=0.01)':<25} | {final_r1:15.6f} | {regs_r1[-1]:12.4f}")
print(f"{'Volterra reg (λ=0.1)':<25} | {final_r2:15.6f} | {regs_r2[-1]:12.4f}")
print(f"{'Volterra reg (λ=1.0)':<25} | {final_r3:15.6f} | {regs_r3[-1]:12.4f}")

print("\n" + "="*72)
print("SINGULAR VALUE STRUCTURE OF IMPULSE KERNEL")
print("="*72)

target = [1.0/(2*k-1) for k in range(1, n_modes+1)]
print(f"\nTarget σ_k/σ_1 = 1/(2k-1):  {[f'{t:.3f}' for t in target]}")

def normalize(svs):
    return [s/svs[0] for s in svs]

print(f"\nBaseline σ_k/σ_1:         {[f'{s:.3f}' for s in normalize(sv_b)]}")
print(f"Volterra λ=0.01 σ_k/σ_1:  {[f'{s:.3f}' for s in normalize(sv_r1)]}")
print(f"Volterra λ=0.1 σ_k/σ_1:   {[f'{s:.3f}' for s in normalize(sv_r2)]}")
print(f"Volterra λ=1.0 σ_k/σ_1:   {[f'{s:.3f}' for s in normalize(sv_r3)]}")

# Compute L2 distance to target for each
def dist_to_target(svs):
    return float(np.sqrt(sum((s/svs[0] - t)**2 for s, t in zip(svs, target))))

print(f"\n{'Variant':<25} | {'L2 dist to Volterra':>20}")
print("-"*55)
print(f"{'Baseline':<25} | {dist_to_target(sv_b):20.4f}")
print(f"{'Volterra λ=0.01':<25} | {dist_to_target(sv_r1):20.4f}")
print(f"{'Volterra λ=0.1':<25} | {dist_to_target(sv_r2):20.4f}")
print(f"{'Volterra λ=1.0':<25} | {dist_to_target(sv_r3):20.4f}")

print("\n" + "="*72)
print("ANALYSIS")
print("="*72)

# Improvement?
best_reg = min(final_r1, final_r2, final_r3)
improvement = (final_b - best_reg) / final_b * 100 if final_b > 0 else 0
print(f"\nBest regularized loss:  {best_reg:.6f}")
print(f"Baseline loss:          {final_b:.6f}")
print(f"Improvement: {improvement:+.2f}%")

if best_reg < final_b:
    print("\n✓ Regularizer IMPROVES baseline. Volterra spectral target is informative.")
else:
    print("\n✗ Regularizer does NOT improve baseline. Either:")
    print("   (a) The copy task doesn't benefit from Volterra-shaped spectrum")
    print("   (b) Wrong regularization strength")
    print("   (c) Volterra target is wrong for this signal")

# Check if regularizer pushed SVs toward target
moved_toward_target = dist_to_target(sv_r2) < dist_to_target(sv_b)
if moved_toward_target:
    print(f"\n✓ Regularizer DID push SVs toward Volterra target (distance reduced)")
else:
    print(f"\n✗ Regularizer did NOT successfully push SVs toward target")

print("\n" + "="*72)
print("VERDICT")
print("="*72)
if best_reg < final_b * 0.9:
    print("STRONG WIN: regularized > 10% improvement. Pursue further.")
elif best_reg < final_b * 0.99:
    print("WEAK WIN: small improvement. Could be noise; need multi-seed validation.")
elif best_reg > final_b * 1.1:
    print("LOSE: regularizer hurt task. Volterra target wrong for this task.")
else:
    print("INCONCLUSIVE: ~tie. Falsifiable with more compute / different tasks.")
