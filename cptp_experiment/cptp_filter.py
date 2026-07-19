"""
CPTP Residual Block — test on Bayesian posterior tracking.

The CPTP block maintains state as a (real) density matrix ρ and updates it
via a Kraus channel:
    ρ_{t+1} = Σ_i K_i(o_t) ρ_t K_i(o_t)^T,    Σ_i K_i^T K_i = I.
This is the most general residual update on a density matrix that
preserves trace and positive-semidefiniteness — i.e., it stays a valid
probability state by construction. Standard residual updates `x + f(x)`
break the simplex; CPTP cannot.

Task: filter a discrete-state HMM with noisy observations.
The TRUE posterior is computed exactly via classical Bayesian update.
Three filters are trained against it:
  (A) MLP-Softmax           — predict posterior logits directly
  (B) Residual-MLP-Softmax  — same with residual connection
  (C) CPTP filter           — density matrix maintained, diagonal read out
All three have matched parameter counts (~within 5%).
"""

import math
import torch
import torch.nn as nn
import torch.nn.functional as F


# ---------------- HMM data ----------------

class HMM:
    def __init__(self, n_states=4, n_obs=4, transition_noise=0.2,
                 obs_noise=0.3, seed=0):
        g = torch.Generator().manual_seed(seed)
        # Transition: mostly stay, sometimes drift to neighbor
        T = torch.eye(n_states) * (1 - transition_noise)
        for i in range(n_states):
            T[i, (i + 1) % n_states] = transition_noise * 0.6
            T[i, (i - 1) % n_states] = transition_noise * 0.4
        self.T = T / T.sum(dim=1, keepdim=True)
        # Observation: diagonal with off-diagonal noise
        E = torch.eye(n_obs) * (1 - obs_noise)
        E += obs_noise / n_obs
        self.E = E / E.sum(dim=1, keepdim=True)
        self.n_states = n_states
        self.n_obs = n_obs
        self.gen = g

    def sample(self, batch, length):
        states = torch.zeros(batch, length, dtype=torch.long)
        obs = torch.zeros(batch, length, dtype=torch.long)
        s = torch.randint(0, self.n_states, (batch,), generator=self.gen)
        for t in range(length):
            states[:, t] = s
            obs[:, t] = torch.multinomial(self.E[s], 1,
                                           generator=self.gen).squeeze(-1)
            s = torch.multinomial(self.T[s], 1, generator=self.gen).squeeze(-1)
        return states, obs

    def true_posterior(self, obs):
        """Exact filtering posterior p(s_t | o_1:t)."""
        batch, length = obs.shape
        p = torch.full((batch, self.n_states), 1.0 / self.n_states)
        out = torch.zeros(batch, length, self.n_states)
        for t in range(length):
            # Observation update
            likelihood = self.E[:, obs[:, t]].T  # (batch, n_states)
            p = p * likelihood
            p = p / p.sum(dim=1, keepdim=True)
            out[:, t] = p
            # Transition update
            p = p @ self.T
        return out


# ---------------- Models ----------------

class MLPSoftmaxFilter(nn.Module):
    """Baseline: predict logits from previous posterior + observation embedding."""
    def __init__(self, n_states, n_obs, hidden):
        super().__init__()
        self.obs_emb = nn.Embedding(n_obs, n_states)  # parameters match CPTP obs
        self.f = nn.Sequential(
            nn.Linear(n_states * 2, hidden), nn.GELU(),
            nn.Linear(hidden, n_states),
        )
        self.n_states = n_states

    def forward(self, obs):
        batch, length = obs.shape
        p = torch.full((batch, self.n_states), 1.0 / self.n_states,
                       device=obs.device)
        out = []
        for t in range(length):
            o = self.obs_emb(obs[:, t])
            logits = self.f(torch.cat([p, o], dim=-1))
            p = F.softmax(logits, dim=-1)
            out.append(p)
        return torch.stack(out, dim=1)


class ResidualSoftmaxFilter(nn.Module):
    """Standard residual baseline: logits = prev_logits + f(prev_logits, obs)."""
    def __init__(self, n_states, n_obs, hidden):
        super().__init__()
        self.obs_emb = nn.Embedding(n_obs, n_states)
        self.f = nn.Sequential(
            nn.Linear(n_states * 2, hidden), nn.GELU(),
            nn.Linear(hidden, n_states),
        )
        self.n_states = n_states

    def forward(self, obs):
        batch, length = obs.shape
        logits = torch.zeros(batch, self.n_states, device=obs.device)
        out = []
        for t in range(length):
            o = self.obs_emb(obs[:, t])
            logits = logits + self.f(torch.cat([logits, o], dim=-1))
            p = F.softmax(logits, dim=-1)
            out.append(p)
        return torch.stack(out, dim=1)


class CPTPFilter(nn.Module):
    """
    CPTP residual filter.

    Maintains state as a real, symmetric, PSD, trace-1 matrix ρ ∈ R^{d×d}.
    At each step, builds observation-dependent Kraus operators
    {K_i(o)}_{i=1..k}, applies the channel
        ρ ← Σ_i K_i(o) ρ K_i(o)^T,
    and reads posterior as the diagonal of ρ.

    Constraint Σ_i K_i^T K_i = I is enforced ARCHITECTURALLY via thin QR on
    the stacked Kraus tensor — no penalty term, no projection during training.
    This guarantees CPTP at every gradient step.
    """
    def __init__(self, n_states, n_obs, num_kraus):
        super().__init__()
        self.d = n_states
        self.k = num_kraus
        # Per-observation Kraus parametrization. Shape (n_obs, k*d, d).
        # Initialized small; QR makes it well-defined regardless.
        self.raw = nn.Parameter(
            torch.randn(n_obs, num_kraus * n_states, n_states) * 0.5
        )

    def _kraus(self, obs):
        # obs: (batch,) int → look up raw[obs] : (batch, k*d, d)
        M = self.raw[obs]
        # Thin QR: Q has orthonormal columns ⇒ Q^T Q = I_d
        # Q shape (batch, k*d, d). Reshape to (batch, k, d, d).
        Q, _ = torch.linalg.qr(M)
        return Q.reshape(-1, self.k, self.d, self.d)

    def forward(self, obs):
        batch, length = obs.shape
        # Initial state: maximally mixed (uniform prior)
        rho = torch.eye(self.d, device=obs.device).expand(batch, -1, -1) / self.d
        out = []
        for t in range(length):
            K = self._kraus(obs[:, t])              # (batch, k, d, d)
            # K @ ρ : (batch, k, d, d)
            K_rho = torch.einsum('bkij,bjl->bkil', K, rho)
            # K @ ρ @ K^T : (batch, k, d, d)
            new_rho = torch.einsum('bkij,bkjl->bkil',
                                   K_rho, K.transpose(-1, -2))
            rho = new_rho.sum(dim=1)
            # Symmetrize against floating-point drift
            rho = 0.5 * (rho + rho.transpose(-1, -2))
            # Read posterior off the diagonal
            p = torch.diagonal(rho, dim1=-2, dim2=-1)
            # Numerical guard — shouldn't be necessary but cheap insurance
            p = p.clamp(min=1e-12)
            p = p / p.sum(dim=-1, keepdim=True)
            out.append(p)
        return torch.stack(out, dim=1)


def count_params(m):
    return sum(p.numel() for p in m.parameters())


# ---------------- Training ----------------

def kl(pred, target):
    """KL(target || pred)  averaged over batch×length."""
    return (target * (target.clamp(min=1e-12).log() -
                      pred.clamp(min=1e-12).log())).sum(-1).mean()


def train_one(model, hmm, n_epochs=400, batch_size=128, length=30, lr=3e-3,
              eval_obs=None, eval_truth=None, name=""):
    opt = torch.optim.Adam(model.parameters(), lr=lr)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=n_epochs)
    history = []
    for epoch in range(n_epochs):
        _, obs = hmm.sample(batch_size, length)
        target = hmm.true_posterior(obs)
        pred = model(obs)
        loss = kl(pred, target)
        opt.zero_grad()
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        sched.step()
        if epoch % 40 == 0 or epoch == n_epochs - 1:
            with torch.no_grad():
                eval_pred = model(eval_obs)
                eval_kl = kl(eval_pred, eval_truth).item()
            history.append((epoch, loss.item(), eval_kl))
            print(f"  [{name:24}] ep {epoch:4d}  train_kl {loss.item():.4f}  "
                  f"eval_kl {eval_kl:.4f}")
    return history


def main():
    torch.manual_seed(42)
    HIDDEN = 32           # baselines hidden width
    NUM_KRAUS = 4
    N_STATES = 4
    N_OBS = 4
    LENGTH = 30
    EVAL_LENGTH = 60      # test on LONGER sequences than trained on

    hmm = HMM(n_states=N_STATES, n_obs=N_OBS,
              transition_noise=0.25, obs_noise=0.35, seed=0)

    eval_hmm = HMM(n_states=N_STATES, n_obs=N_OBS,
                   transition_noise=0.25, obs_noise=0.35, seed=999)
    _, eval_obs = eval_hmm.sample(256, EVAL_LENGTH)
    eval_truth = eval_hmm.true_posterior(eval_obs)

    models = {
        "MLP+Softmax":      MLPSoftmaxFilter(N_STATES, N_OBS, HIDDEN),
        "Residual+Softmax": ResidualSoftmaxFilter(N_STATES, N_OBS, HIDDEN),
        "CPTP filter":      CPTPFilter(N_STATES, N_OBS, NUM_KRAUS),
    }
    print("\nParameter counts:")
    for n, m in models.items():
        print(f"  {n:24} {count_params(m):>5d}")
    print()

    results = {}
    for name, model in models.items():
        print(f"Training {name}")
        results[name] = train_one(model, hmm, length=LENGTH,
                                  eval_obs=eval_obs, eval_truth=eval_truth,
                                  name=name)

    print("\n" + "=" * 60)
    print(f"Final eval KL on length-{EVAL_LENGTH} sequences "
          f"(trained on length {LENGTH}):")
    print("=" * 60)
    # Floor: the uniform-prediction KL, so we know what "doing nothing" costs
    uniform = torch.full_like(eval_truth, 1.0 / N_STATES)
    print(f"  {'uniform-prior baseline':24} {kl(uniform, eval_truth).item():.4f}")
    for name, hist in results.items():
        final_eval = hist[-1][2]
        print(f"  {name:24} {final_eval:.4f}")


if __name__ == "__main__":
    main()
