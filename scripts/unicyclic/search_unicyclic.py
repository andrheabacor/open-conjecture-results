"""Exploratory exact counts for connected zero forcing of unicyclic graphs."""
from random import Random


def adjacency(n, edges):
    neighbors = [0] * n
    for u, v in edges:
        neighbors[u] |= 1 << v
        neighbors[v] |= 1 << u
    return neighbors


def counts(n, edges):
    neighbors = adjacency(n, edges)
    all_vertices = (1 << n) - 1
    coefficients = [0] * (n + 1)
    force = bytearray(1 << n)
    force[all_vertices] = 1
    # Every legal force gives a strictly larger mask, already computed in this order.
    for s in range(all_vertices, 0, -1):
        if s != all_vertices:
            todo = s
            while todo:
                u = todo & -todo
                todo -= u
                white = neighbors[u.bit_length() - 1] & ~s
                if white.bit_count() == 1:
                    force[s] = force[s | white]
                    break
        if not force[s]:
            continue
        reached = frontier = s & -s
        while frontier:
            u = frontier & -frontier
            frontier -= u
            new = neighbors[u.bit_length() - 1] & s & ~reached
            frontier |= new
            reached |= new
        if reached == s:
            coefficients[s.bit_count()] += 1
    return coefficients


def cycle(m):
    return [(j, (j + 1) % m) for j in range(m)]


def failure(a):
    return [i for i in range(1, len(a) - 1) if a[i] ** 2 < a[i - 1] * a[i + 1]]


if __name__ == "__main__":
    examples = [
        ([(0, 1), (1, 2), (2, 3)], [0, 2, 3, 2, 1]),
        ([(0, 1), (0, 2), (0, 3)], [0, 0, 0, 3, 1]),
    ]
    for edges, expected in examples:
        actual = counts(4, edges)
        assert actual == expected
        print("source example", edges, actual, flush=True)
    rng = Random(176)
    for n in range(4, 18):
        tried = set()
        for m in range(3, n + 1):
            for sample in range(55):
                edges = cycle(m)
                for v in range(m, n):
                    if sample == 0:
                        u = 0
                    elif sample == 1:
                        u = v - 1 if v > m else 0
                    elif sample == 2:
                        u = (v - m) % m
                    elif sample == 3:
                        u = (v - m) % 2
                    elif sample < 24:
                        u = rng.randrange(m)
                    else:
                        u = rng.randrange(v)
                    edges.append((u, v))
                labelled_graph = tuple(edges)
                if labelled_graph in tried:
                    continue
                tried.add(labelled_graph)
                coefficients = counts(n, edges)
                violations = failure(coefficients)
                if violations:
                    print("failure", n, m, edges, coefficients, violations, flush=True)
                    raise SystemExit
        print("tested", n, len(tried), flush=True)
