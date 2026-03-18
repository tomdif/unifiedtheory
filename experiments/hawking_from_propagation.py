#!/usr/bin/env python3
"""
Hawking temperature from the derived propagation rule.

PROPER COMPUTATION:
1. Solve the null geodesic equation in Schwarzschild exactly (ODE)
2. Compute the coordinate time delay (the source functional value)
3. Sum amplitudes e^{ikφ} over paths near the photon sphere
4. Check spectrum against Planck distribution

The key physics: near the photon sphere r=3M, the time delay
diverges logarithmically: Δt ~ -(1/κ_eff) ln(b/b_c - 1) + const
where κ_eff is related to the Lyapunov exponent of the photon orbit.

For the photon sphere: κ_eff = 1/(3√3 M) (the Lyapunov exponent).
The Hawking temperature uses the surface gravity κ = 1/(4M).
These are different — the photon sphere gives κ_eff, not κ.

The actual Hawking derivation uses modes near the EVENT HORIZON (r=2M),
not the photon sphere (r=3M). Our sum-over-paths naturally samples
the photon sphere. The connection to Hawking temperature requires
tracing modes from the photon sphere back to the horizon.
"""

import numpy as np
from scipy.integrate import solve_ivp
import sys

# ============================================================
# Exact null geodesic solver
# ============================================================

def null_geodesic_time_delay(M, b, r_start=500.0):
    """Compute the coordinate time delay Δt for a null ray in
    Schwarzschild geometry with mass M, impact parameter b.

    The null geodesic equations (using u = 1/r, φ as parameter):
    (du/dφ)² = 1/b² - u² + 2Mu³

    The coordinate time integral:
    Δt = ∫ dt = ∫ (E/f²) / (L·|du/dφ|) dφ  where f = 1-2Mu

    We integrate the ODE for u(φ) and accumulate the time.
    """
    b_crit = 3 * np.sqrt(3) * M

    if b <= b_crit:
        return None  # Captured

    # Effective potential
    # (du/dφ)² = h(u) where h(u) = 1/b² - u² + 2M u³
    # Turning point: h(u_turn) = 0

    # Find turning point numerically
    from scipy.optimize import brentq

    def h(u):
        return 1/b**2 - u**2 + 2*M*u**3

    # u_turn is the largest root of h(u) = 0 with u < 1/(2M)
    # For b > b_crit, there's a turning point between 0 and 1/(3M)
    try:
        u_turn = brentq(h, 0, 1/(3*M) - 1e-10)
    except ValueError:
        # No turning point found — try wider range
        try:
            u_turn = brentq(h, 0, 1/(2.01*M))
        except ValueError:
            return None

    # Integrate from u=0 (r=∞) to u_turn and back
    # Total time delay = 2 × ∫₀^{u_turn} dt/du du (by symmetry)

    # dt/dφ = E/(f·L) where E/L = 1/b and f = 1-2Mu
    # du/dφ = ±√h(u)
    # So dt = (1/b) / ((1-2Mu)² · √h(u)) · (1-2Mu) du
    # Wait, let me redo this carefully.

    # For null geodesics: ds²=0 gives
    # (1-2M/r)dt = ... complicated in r
    # Better to use the standard result:
    # dt/dφ = b/(1-2M/r) · (1/r²) / |dr/dφ| ... still messy

    # Cleanest: use the time integral directly
    # Δt = 2∫_{r_turn}^{r_max} dr / ((1-2M/r) · √(1 - b²(1-2M/r)/r²))
    # where the integrand comes from dt/dr for null rays

    r_turn = 1/u_turn
    r_max = r_start

    # Numerical integration with careful handling near turning point
    n_points = 50000
    # Use substitution r = r_turn + s² to handle the square-root singularity
    s_max = np.sqrt(r_max - r_turn)
    s_values = np.linspace(1e-8, s_max, n_points)
    ds = s_values[1] - s_values[0]

    delta_t = 0.0
    delta_t_flat = 0.0  # Flat-space comparison

    for s in s_values:
        r = r_turn + s**2
        f = 1 - 2*M/r
        if f <= 0:
            continue

        # Effective potential discriminant
        disc = 1/b**2 - f/r**2
        if disc <= 0:
            continue

        # dt/dr = 1/(f · √(1/b² - f/r²)) for null rays
        # But we're integrating in s where r = r_turn + s²
        # dr/ds = 2s
        dt_dr = 1.0 / (f * b * np.sqrt(disc))
        dr_ds = 2 * s

        delta_t += dt_dr * dr_ds * ds

        # Flat space comparison (M=0): dt/dr = 1/√(1 - b²/r²)
        disc_flat = 1/b**2 - 1/r**2
        if disc_flat > 0:
            delta_t_flat += (1.0 / (b * np.sqrt(disc_flat))) * dr_ds * ds

    # Factor of 2 for both legs (approach + departure)
    delta_t *= 2
    delta_t_flat *= 2

    # The TIME DELAY relative to flat space is the physically meaningful quantity
    # This is what the source functional measures as the "extra phase"
    time_delay = delta_t - delta_t_flat

    return time_delay


def compute_spectrum(M, omega_values, n_paths=1000):
    """Compute the amplitude spectrum from sum over paths near the photon sphere."""
    b_crit = 3 * np.sqrt(3) * M

    # Sample impact parameters logarithmically near b_crit
    db_min, db_max = 1e-4 * M, 10.0 * M
    db_values = np.logspace(np.log10(db_min), np.log10(db_max), n_paths)
    b_values = b_crit + db_values

    # Compute time delay for each path
    delays = np.zeros(n_paths)
    valid = np.ones(n_paths, dtype=bool)

    print(f"  Computing {n_paths} geodesics...", end="", flush=True)
    for i, b in enumerate(b_values):
        td = null_geodesic_time_delay(M, b)
        if td is None:
            valid[i] = False
        else:
            delays[i] = td
    print(f" done. {valid.sum()} valid paths.")

    if valid.sum() < 10:
        print("  Too few valid paths!")
        return None

    delays = delays[valid]
    db_valid = db_values[valid]

    # Check logarithmic scaling: Δt ~ -C · ln(db) + const
    log_db = np.log(db_valid)
    # Linear fit: delays = a·log_db + c
    coeffs = np.polyfit(log_db, delays, 1)
    slope = coeffs[0]

    # For photon sphere: the Lyapunov exponent λ_L = 1/(3√3 M)
    # Time delay: Δt ~ -(1/λ_L) ln(b-b_c) = -3√3 M ln(b-b_c)
    lyapunov = 1 / (3 * np.sqrt(3) * M)
    predicted_slope = -1 / lyapunov  # = -3√3 M

    print(f"  Time delay range: [{delays.min():.2f}, {delays.max():.2f}]")
    print(f"  Log slope: measured={slope:.4f}, predicted(-3√3M)={predicted_slope:.4f}, ratio={slope/predicted_slope:.4f}")

    # Compute amplitudes: Z(ω) = Σ e^{iω·Δt} · weight
    # Weight proportional to db (uniform measure in impact parameter)
    weights = db_valid / db_valid.sum()

    Z = np.zeros(len(omega_values), dtype=complex)
    for j, omega in enumerate(omega_values):
        Z[j] = np.sum(weights * np.exp(1j * omega * delays))

    power = np.abs(Z)**2
    return power, delays, db_valid, slope, predicted_slope


def main():
    print("=" * 65)
    print("HAWKING RADIATION FROM DERIVED PROPAGATION RULE")
    print("Exact null geodesics in Schwarzschild geometry")
    print("=" * 65)

    for M in [1.0, 2.0, 5.0]:
        print(f"\n{'='*65}")
        print(f"M = {M}")
        print(f"{'='*65}")

        kappa = 1 / (4*M)  # Surface gravity
        T_H = kappa / (2*np.pi)  # Hawking temperature
        lyapunov = 1/(3*np.sqrt(3)*M)  # Photon sphere Lyapunov exponent
        T_photon = lyapunov / (2*np.pi)  # "Temperature" from photon sphere

        print(f"  Surface gravity κ = {kappa:.6f}")
        print(f"  Hawking T_H = κ/(2π) = {T_H:.6f}")
        print(f"  Lyapunov λ_L = {lyapunov:.6f}")
        print(f"  Photon sphere T = λ_L/(2π) = {T_photon:.6f}")

        # Frequency range: sample around BOTH temperatures
        omega_max = 5 * max(T_H, T_photon)
        omega_values = np.linspace(0.001, omega_max, 100)

        result = compute_spectrum(M, omega_values, n_paths=2000)
        if result is None:
            continue

        power, delays, db, slope, pred_slope = result

        # Compare with Planck at Hawking temperature
        planck_H = 1.0 / (np.exp(omega_values / T_H) - 1 + 1e-30)
        # Compare with Planck at photon-sphere temperature
        planck_P = 1.0 / (np.exp(omega_values / T_photon) - 1 + 1e-30)

        # Normalize
        pn = power / (power.max() + 1e-30)
        ph = planck_H / (planck_H.max() + 1e-30)
        pp = planck_P / (planck_P.max() + 1e-30)

        corr_H = np.corrcoef(pn, ph)[0,1]
        corr_P = np.corrcoef(pn, pp)[0,1]

        print(f"\n  Correlation with Planck(T_Hawking): {corr_H:.4f}")
        print(f"  Correlation with Planck(T_photon):  {corr_P:.4f}")

        # The photon sphere temperature should be the better fit
        # because our paths sample the photon sphere, not the event horizon
        print(f"\n  {'ω':>8} {'|Z|²':>10} {'Planck_H':>10} {'Planck_P':>10}")
        for i in range(0, len(omega_values), 10):
            print(f"  {omega_values[i]:>8.4f} {pn[i]:>10.4f} {ph[i]:>10.4f} {pp[i]:>10.4f}")

    print(f"\n{'='*65}")
    print("NOTE: The sum-over-paths samples the PHOTON SPHERE (r=3M),")
    print("not the event horizon (r=2M). The relevant temperature is")
    print("T_photon = λ_L/(2π) = 1/(6π√3 M), not T_Hawking = 1/(8πM).")
    print("These differ by a factor of 4/(3√3) ≈ 0.77.")
    print("The connection to Hawking temperature requires tracing modes")
    print("from the photon sphere back to the horizon, which involves")
    print("the gravitational redshift factor √(f(3M)/f(r→∞)) = √(1/3).")
    print("=" * 65)


if __name__ == "__main__":
    main()
