"""
verify_near_vacuum.py — Verify the dimensional ladder conjecture

For [m]^d, the near-vacuum count CC_{m^d - k}([m]^d) should equal
the self-convolution (P_{d-1} * P_{d-1})(k), where P_{d-1} counts
(d-1)-dimensional partitions.

d=2: P_1 = ordinary partitions, GF = η(q)^{-2}        [PROVED in Lean]
d=3: P_2 = plane partitions,   GF = D_2(q)^2           [verify here]
d=4: P_3 = solid partitions,   GF = D_3(q)^2           [verify here]
"""

from itertools import product as cartesian_product
from functools import lru_cache

# --- Partition counts ---

@lru_cache(maxsize=None)
def partition_count(n):
    """Number of ordinary partitions of n."""
    if n < 0: return 0
    if n == 0: return 1
    result = 0
    for k in range(1, n + 1):
        sign = (-1) ** (k + 1)
        g1 = k * (3 * k - 1) // 2
        g2 = k * (3 * k + 1) // 2
        result += sign * (partition_count(n - g1) + partition_count(n - g2))
    return result

# Plane partition counts (A000219)
PLANE_PARTITIONS = [1, 1, 3, 6, 13, 24, 48, 86, 160, 282, 500, 859,
                    1479, 2485, 4167, 6879, 11297, 18334, 29601, 47330]

# Solid partition counts (A000293)
SOLID_PARTITIONS = [1, 1, 4, 10, 26, 59, 140, 307, 684, 1464, 3122,
                    6500, 13426, 27248, 54804, 108802, 214071, 416849]

def get_partition_counts(dim, max_k):
    """Get partition counts for dimension dim, up to k=max_k."""
    if dim == 1:
        return [partition_count(k) for k in range(max_k + 1)]
    elif dim == 2:
        return PLANE_PARTITIONS[:max_k + 1]
    elif dim == 3:
        return SOLID_PARTITIONS[:max_k + 1]
    else:
        raise ValueError(f"No partition data for dim={dim}")

def self_convolution(counts, k):
    """(P * P)(k) = sum_{j=0}^{k} P(j) * P(k-j)."""
    return sum(counts[j] * counts[k - j] for j in range(k + 1))

# --- Convex subset counting ---

def is_convex(S, d, m):
    """Check if S (a set of d-tuples) is order-convex in [m]^d."""
    for a in S:
        for c in S:
            if all(a[i] <= c[i] for i in range(d)):
                # Check all b with a <= b <= c are in S
                ranges = [range(a[i], c[i] + 1) for i in range(d)]
                for b in cartesian_product(*ranges):
                    if b not in S:
                        return False
    return True

def count_convex_of_size(d, m, size):
    """Count convex subsets of [m]^d of given size."""
    points = list(cartesian_product(range(m), repeat=d))
    n = len(points)
    point_set = set(points)

    if size == n:
        return 1  # Only the full set
    if size == 0:
        return 1  # Only the empty set

    # For near-vacuum (size close to n), enumerate by what's REMOVED
    removed = n - size
    if removed <= 6 and n <= 64:
        from itertools import combinations
        count = 0
        for combo in combinations(range(n), removed):
            S = set(points) - {points[i] for i in combo}
            if is_convex(S, d, m):
                count += 1
        return count

    return -1  # Too large to enumerate

def main():
    print("=" * 72)
    print("NEAR-VACUUM DIMENSIONAL LADDER VERIFICATION")
    print("=" * 72)

    for grid_d in [2, 3, 4]:
        part_dim = grid_d - 1  # P_{d-1}
        max_k = min(8, len(get_partition_counts(part_dim, 20)) - 1)
        counts = get_partition_counts(part_dim, max_k)

        print(f"\n{'─' * 72}")
        dim_name = {1: "ordinary", 2: "plane", 3: "solid"}[part_dim]
        print(f"[m]^{grid_d}: P_{part_dim} = {dim_name} partitions")
        print(f"Conjecture: CC_{{m^{grid_d}-k}}([m]^{grid_d}) = (P_{part_dim}*P_{part_dim})(k)")
        print(f"{'─' * 72}")

        # Print predicted values
        predicted = [self_convolution(counts, k) for k in range(min(max_k + 1, 10))]
        print(f"Predicted: {predicted}")

        # Verify for small m
        m_range = range(2, min(5 if grid_d <= 3 else 4, 6))
        for m in m_range:
            n = m ** grid_d
            if n > 64:
                print(f"  m={m}: n={n} (too large for exhaustive check)")
                continue

            print(f"  m={m}: n={n}")
            max_k_check = min(6, n - 1, max_k)
            all_match = True
            for k in range(max_k_check + 1):
                if k >= m:
                    break  # Need m > k
                cc = count_convex_of_size(grid_d, m, n - k)
                pred = self_convolution(counts, k)
                match = "✓" if cc == pred else "✗"
                if cc != pred:
                    all_match = False
                print(f"    k={k}: CC_{{{n}-{k}}}={cc}, (P*P)({k})={pred}  {match}")
            if all_match:
                print(f"    → All verified ✓")

    print(f"\n{'=' * 72}")
    print("SUMMARY")
    print("=" * 72)

    # Print the novel sequences
    for grid_d, part_dim in [(3, 2), (4, 3)]:
        counts = get_partition_counts(part_dim, 15)
        seq = [self_convolution(counts, k) for k in range(min(16, len(counts)))]
        dim_name = {2: "plane", 3: "solid"}[part_dim]
        print(f"\n[m]^{grid_d} near-vacuum ({dim_name}×{dim_name}):")
        print(f"  {seq}")

if __name__ == "__main__":
    main()
