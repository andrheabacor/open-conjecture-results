"""Independent graph counts and exact disk checks for the connected domination polynomial."""
from itertools import combinations
from math import comb, gcd


def by_neighborhoods(n, edges):
    full = (1 << n) - 1
    neighbors = [0] * n
    for u, v in edges:
        neighbors[u] |= 1 << v
        neighbors[v] |= 1 << u
    good = set()
    for s in range(1, full + 1):
        seen = s & -s
        reached = seen
        while seen:
            v = seen & -seen
            seen ^= v
            new = s & neighbors[v.bit_length() - 1] & ~reached
            seen |= new
            reached |= new
        if reached == s and all((s & (1 << v)) or (s & neighbors[v]) for v in range(n)):
            good.add(s)
    return good


def by_spanning_trees(n, edges):
    # For n>=3 the non-leaves of every spanning tree dominate and are connected.
    # Conversely, extend any tree on a connected dominating set by one leaf for each outsider.
    if n == 1:
        return {1}
    if n == 2:
        return {1, 2, 3} if edges else set()
    cores = set()
    for candidate in combinations(edges, n - 1):
        labels = list(range(n))
        degrees = [0] * n
        for u, v in candidate:
            a, b = labels[u], labels[v]
            if a == b:
                break
            labels = [a if x == b else x for x in labels]
            degrees[u] += 1
            degrees[v] += 1
        else:
            cores.add(sum(1 << v for v, deg in enumerate(degrees) if deg >= 2))
    return {s for s in range(1 << n) if any(s & core == core for core in cores)}


def exact_schur_disk(coefficients, numerator, denominator):
    """Schur recursion on the integer polynomial denominator^n P(numerator*w/denominator-1)."""
    n = len(coefficients) - 1
    row = [numerator**j * denominator**(n-j) *
           sum(comb(k, j) * (-1)**(k-j) * coefficients[k] for k in range(j, n+1))
           for j in range(n+1)]
    while len(row) > 1:
        low, high = row[0], row[-1]
        if abs(low) >= abs(high):
            return False
        row = [high * row[i] - low * row[-i-1] for i in range(1, len(row))]
        common = gcd(*row)
        row = [x // common for x in row]
    return row[0] != 0


def check(n, edges, expected=None):
    good = by_neighborhoods(n, edges)
    assert good == by_spanning_trees(n, edges), (n, edges, 'two algorithms disagree')
    if (1 << n) - 1 not in good:
        return None
    counts = [sum(s.bit_count() == k for s in good) for k in range(n+1)]
    if expected is not None:
        assert counts == expected, (counts, expected)
    min_degree = min(sum(v in e for e in edges) for v in range(n))
    threshold = max(1, 2 * min_degree + 2 - n)
    assert all(s in good for s in range(1 << n) if n - s.bit_count() < threshold)
    assert exact_schur_disk(counts, 4 * n, threshold), (n, edges, counts)
    return counts


def cycle(n):
    return [(i, (i+1) % n) for i in range(n)]


if __name__ == '__main__':
    # Reproduce the printed controls before the new graph checks.
    examples = [
        ('P3 (Example 2.2)', 3, [(0, 1), (1, 2)], [0, 1, 2, 1]),
        ('P3[K2] (Example 2.2)', 6,
         [(u, v) for u, v in combinations(range(6), 2) if abs(u//2 - v//2) <= 1],
         [0, 2, 9, 16, 14, 6, 1]),
        ('C4 (cycle lemma)', 4, cycle(4), [0, 0, 4, 4, 1]),
        ('C5 (cycle lemma)', 5, cycle(5), [0, 0, 0, 5, 5, 1]),
    ]
    for title, n, edges, expected in examples:
        print(title, check(n, edges, expected))
    for n in range(1, 7):
        edges = list(combinations(range(n), 2))
        connected = 0
        for mask in range(1 << len(edges)):
            graph = [e for i, e in enumerate(edges) if mask >> i & 1]
            connected += check(n, graph) is not None
        print(f'n={n}: {1 << len(edges)} labelled graphs, {connected} connected,'
              ' both subset families agree; every connected graph passed exact disk check')
