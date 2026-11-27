"""Verify the article's examples and the counterexample by two independent algorithms.

Run with Python 3.10 or later. Only the standard library is needed.
"""
from itertools import combinations

from search_unicyclic import counts


def subsets(vertices):
    for size in range(len(vertices) + 1):
        yield from map(frozenset, combinations(vertices, size))


def fort_counts(order, edges):
    """Test forcing by disjoint forts, and connectivity by crossing every proper cut."""
    vertices = frozenset(range(order))
    # Use unordered pairs and ordinary sets, independently of the bit-mask implementation.
    pairs = {frozenset(edge) for edge in edges}
    neighbors = {v: {u for u in vertices if {u, v} in pairs} for v in vertices}
    forts = [
        f for f in subsets(vertices)
        if f and all(len(neighbors[v] & f) != 1 for v in vertices - f)
    ]
    result = [0] * (order + 1)
    for s in subsets(vertices):
        if not s or any(s.isdisjoint(f) for f in forts):
            continue
        if all(
            any(neighbors[u] & (s - side) for u in side)
            for side in subsets(s) if side and side != s
        ):
            result[len(s)] += 1
    return result


def tadpole_counts_by_arcs(cycle_length):
    """Count cycle arcs and permissible initial segments of the attached two-edge path."""
    result = [0] * (cycle_length + 3)
    for size in range(2, cycle_length + 1):
        full = size == cycle_length
        result[size] += 1 if full else cycle_length
        containing_attachment = 1 if full else size
        result[size + 1] += containing_attachment
        result[size + 2] += containing_attachment
    return result


def check(name, n, edges, expected):
    dynamics = counts(n, edges)
    forts = fort_counts(n, edges)
    assert dynamics == forts == expected, (name, dynamics, forts, expected)
    print(f"{name}: {dynamics}")


if __name__ == "__main__":
    check("Section 5, path P4", 4, [(0,1), (1,2), (2,3)], [0,2,3,2,1])
    check("Section 5, star K1,3", 4, [(0,1), (0,2), (0,3)], [0,0,0,3,1])
    spider = [(0,1), (0,2), (0,3), (0,4), (0,5), (1,6), (2,7), (3,8)]
    check("Example 5.17, Case I, uniform starlike tree", 9, spider,
          [0,0,0,0,0,5,13,12,5,1])
    for m in range(5, 10):
        # Match the Lean labels: attachment at m-1, then tail vertices m and m+1.
        edges = [(i, i + 1) for i in range(m + 1)] + [(0, m - 1)]
        coeffs = tadpole_counts_by_arcs(m)
        check(f"C{m} with two-edge tail", m + 2, edges, coeffs)
        assert (coeffs[2], coeffs[3], coeffs[4]) == (m, m + 2, m + 5)
        assert coeffs[2] * coeffs[4] - coeffs[3] ** 2 == m - 4
