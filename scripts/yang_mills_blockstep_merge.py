"""Collect the runs of yang_mills_blockstep_rp_probe.py into one data file (numerics, not a proof).
Usage: first_run_dir second_run_dir out.json

Runs in first_run_dir: the earlier heatbath runs, whose thermalization and raw series were not recorded, and the rank runs.
Runs in second_run_dir: chains with recorded seed, thermalization, bin dependence and autocorrelation."""
import sys, json, os

d1, d2, out = sys.argv[1], sys.argv[2], sys.argv[3]
def load(d, f):
    p = os.path.join(d, f)
    return json.load(open(p)) if os.path.exists(p) else None

res = dict(note='Numerics only. RP requires C0*C2 >= C1^2 for the winding correlator at coarse times 0, 1, 2 on T > L; on T = L the '
                'two-slice form (C0 + C2) C2 >= 2 C1^2 is the one to use, since C2 carries its periodic image there. C2*C4 >= C3^2 is '
                'the open-half version. iso is TwistedBlockMap; aniso drops time staples on spatial links; half keeps the first link '
                'raw and averages the second with staples that avoid first links.')
res['free_ratios'] = load(d1, 'f32.json')
res['free_hankel'] = load(d2, 'h3.json')
res['free_two_weights'] = load(d2, 'two2.json')
res['rank_n4_alpha_015'] = load(d1, 'rank4.json')
res['rank_n6_alpha_015'] = load(d1, 'rank6.json')
res['rank_n4_alpha_1'] = load(d1, 'rank4b.json')
res['interp_check'] = load(d2, 'interp.json')
res['mc_earlier'] = dict(note='Earlier runs. Thermalization and raw series not recorded. L=8, T=24, not the hypercubic lattice of the Lean '
                              'theorems. The runs at beta_std 16 with alpha 0.25 and 0.15 reuse one seed and chain, so they are not independent.',
                         alpha_025=load(d1, 'mc_a25_long.json'), alpha_015=load(d1, 'mc_a15.json'))
res['mc_rerun_independent_reviewer'] = dict(note='Independent chain, seed 987654, ntherm 100, 1600 measurements, L=8, T=24, beta_std 16.',
                                            summary=load(d2, 'mc_reviewer.json'))
res['mc_T24'] = load(d2, 'mc_T24.json')
res['mc_T8_hypercubic'] = load(d2, 'mc_T8.json')
res['mc_T8_hypercubic_beta64'] = load(d2, 'mc_T8_b64.json')

# independent chains at L=8, T=24, beta_std=16, each with its own seed
def combine(entries):
    w = sum(1 / e ** 2 for _, e in entries)
    return dict(mean=sum(r / e ** 2 for r, e in entries) / w, err=w ** -0.5, chi2=sum((r - sum(a / b ** 2 for a, b in entries) / w) ** 2 / e ** 2 for r, e in entries), chains=len(entries))
comb = {}
early = {('iso', 0.15): None, ('aniso', 0.15): None, ('iso', 0.25): None}
for r in (res['mc_earlier']['alpha_015'] or []):
    if r['beta_std'] == 16.0 and (r['map'], r['alpha']) in early:
        early[(r['map'], r['alpha'])] = (r['ratio'], r['err'])
for r in (res['mc_earlier']['alpha_025'] or []):
    if r['beta_std'] == 16.0 and (r['map'], r['alpha']) in early:
        early[(r['map'], r['alpha'])] = (r['ratio'], r['err'])
rev = res['mc_rerun_independent_reviewer']['summary'] or {}
new = (res['mc_T24'] or {}).get('maps', {})
for label, key, rk in (('iso:0.15', ('iso', 0.15), 'iso15'), ('iso:0.25', ('iso', 0.25), 'iso25'), ('aniso:0.15', ('aniso', 0.15), 'an15')):
    ent = []
    if label in new: ent.append((new[label]['ratio'], new[label]['err_by_nbins']['40']))
    if rk in rev: ent.append((rev[rk]['ratio'], rev[rk]['err_by_nbins']['40']))
    if early[key]: ent.append(early[key])
    if ent: comb[label] = combine(ent)
res['mc_T24_combined_independent_chains'] = dict(note='Inverse-variance mean. The earlier iso 0.15 and iso 0.25 entries at beta_std 16 share a chain with each other, not with the others.', **comb)
json.dump(res, open(out, 'w'), indent=1)
print({k: (v is not None) for k, v in res.items() if k != 'note'})
print(json.dumps(comb, indent=1))
