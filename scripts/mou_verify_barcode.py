"""Independent finite checks for Mou's Conjecture 1.4, using only Python stdlib."""

from collections import Counter
from itertools import combinations, permutations, product
from math import comb


def extensions_by_filter(size, strict_pairs):
    for word in permutations(range(size)):
        position = {value: i for i, value in enumerate(word)}
        if all(position[i] < position[j] for i, j in strict_pairs):
            yield word


def witness_extensions_by_insertion():
    # Choose ordered slots for the two isolated elements. The chain fills the rest.
    for first, second in permutations(range(7), 2):
        chain = iter(range(5))
        yield tuple(5 if i == first else 6 if i == second else next(chain) for i in range(7))


def descent_counts(words):
    return Counter(sum(a > b for a, b in zip(word, word[1:])) for word in words)


def run():
    pairs = list(combinations(range(5), 2))
    words = set(extensions_by_filter(7, pairs))
    assert words == set(witness_extensions_by_insertion())
    hist = descent_counts(words)
    assert hist == {0: 1, 1: 16, 2: 25}
    print("Linear extensions (permutation filter and insertion):", len(words), sorted(hist.items()))

    # First endpoint method: directly count strict maps, with a separate product formula.
    strict_maps = [
        sum(all(v[i] < v[j] for i, j in pairs) for v in product(range(q), repeat=7))
        for q in range(6)
    ]
    assert strict_maps == [comb(q, 5)*q*q for q in range(6)] == [0, 0, 0, 0, 0, 25]
    endpoint_from_strict_maps = strict_maps[5], sum(strict_maps[:5])
    print("Strict maps for q=0..5 (enumeration and product formula):", strict_maps)

    # Second endpoint method: fill five whole periods of actual binomial bars.
    periods = [
        (sum(count*comb(x+t, 6) for x, count in hist.items()),
         sum(count*comb(x+t, 7) for x, count in hist.items()))
        for t in range(5)
    ]
    endpoint_from_bars = tuple(map(sum, zip(*periods)))
    assert endpoint_from_strict_maps == endpoint_from_bars == (25, 0)
    print("Periods (length, contribution):", periods, "endpoint:", endpoint_from_bars)

    # Enumerate monotone binary functions by constraints and by independent thresholds.
    vertices = {v for v in product(range(2), repeat=7) if all(v[i] <= v[j] for i, j in pairs)}
    thresholds = {
        (0,)*zeros + (1,)*(5-zeros) + free
        for zeros in range(6) for free in product(range(2), repeat=2)
    }
    assert vertices == thresholds and len(vertices) == 24
    points = vertices | {(2,)*7}
    assert len(points) == 25 and vertices <= points
    print("Vertices (bit constraints and thresholds):", len(vertices), "points:", len(points))

    # A homothety is fixed by the images of the zero and all-ones vertices.
    # Exhaust all ordered pairs of distinct points to count copies in this particular S.
    copies = []
    for u, w in permutations(points, 2):
        scale = w[0] - u[0]
        if scale > 0 and all(b-a == scale for a, b in zip(u, w)):
            if all(tuple(a+scale*b for a, b in zip(u, v)) in points for v in vertices):
                copies.append((u, scale))
    assert copies == [((0,)*7, 1)]
    print("Copies in the displayed 25-point set:", copies)

    cases = [
        ("chain on three", 3, list(combinations(range(3), 2)), [0]),
        ("antichain on two", 2, [], [0, 1]),
        ("ordinal sum of two antichains on two", 4, list(product(range(2), range(2, 4))),
         [0, 1, 1, 2]),
    ]
    for name, size, strict, expected in cases:
        values = sorted(descent_counts(extensions_by_filter(size, strict)).elements())
        assert values == expected
        print("Theorem 1.3:", name, values)

    # Direct geometric enumeration of the two square configurations in Figure 4.
    for r, expected in [(3, 17), (6, 21)]:
        extra = [(4, j) for j in range(4)] + [(i, 4) for i in range(5)]
        square_points = set(product(range(4), repeat=2)) | set(extra[:r])
        squares = sum({(x+s, y), (x, y+s), (x+s, y+s)} <= square_points
                      for x, y in square_points for s in range(1, 5))
        by_formula = sum(j*j for j in range(1, 4)) + comb(min(r, 4), 2) + comb(max(0, r-4), 2)
        assert squares == by_formula == expected
        print("Square example (points, copies):", len(square_points), squares)


if __name__ == "__main__":
    run()
