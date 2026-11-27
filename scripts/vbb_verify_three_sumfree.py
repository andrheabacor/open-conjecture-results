"""Two independent integer algorithms for the paper's strict three-sumfree recurrence."""
from itertools import combinations

def scan_candidates(seeds, terms):
    """Test each new integer against all triples of earlier, distinct entries."""
    values = list(seeds)
    candidate = values[-1]
    while len(values) < terms:
        candidate += 1
        if all(a+b+c != candidate for a,b,c in combinations(values,3)):
            values.append(candidate)
    return values

def bits_next(seeds, terms):
    """Maintain bit sets for sums of one, two and three different accepted values."""
    ones = pairs = triples = 0
    def extend(n):
        nonlocal ones, pairs, triples
        triples |= pairs << n
        pairs |= ones << n
        ones |= 1 << n
    for n in seeds:
        extend(n)
    values = list(seeds)
    while len(values) < terms:
        n = values[-1]
        tail = triples >> (n+1)
        # If exactly r consecutive low bits are set, this expression is r+1.
        advance = (tail ^ (tail+1)).bit_length()
        n += advance
        extend(n)
        values.append(n)
    return values

def both(seeds, terms):
    a = scan_candidates(seeds, terms)
    b = bits_next(seeds, terms)
    assert a == b, (seeds, a, b)
    return a

def main():
    s = both((1,3,7), 20)
    assert s[:13] == [1,3,7,8,9,10,15,29,35,36,56,62,63]
    assert (s[8]-s[7],s[12]-s[11]) == (6,1)
    print("d=4, first 13 entries:", s[:13])
    print("One-indexed D8, D12:", s[8]-s[7], s[12]-s[11])
    print("One-indexed s8, s12 and shift:", s[7], s[11], s[11]-s[7])
    for d in (6,29):
        k = d+3
        s = both((1,d-1,2*d-1), k+d+2)
        predicted, observed = 8*d-1, s[k+d]-s[k]
        assert predicted != observed
        print(f"d={d}, s[{k+1}]={s[k]}, s[{k+d+1}]={s[k+d]}, "
              f"observed shift {observed}, conjectured shift {predicted}")
    table = [((1,2,6),6,6,28), ((1,2,7),8,8,44), ((1,3,8),8,6,38)]
    for seeds,k,p,modulus in table:
        seq = both(seeds,k+4*p+1)
        gaps = [b-a for a,b in zip(seq,seq[1:])]
        start, end = k, k+3*p
        assert gaps[start:end] == gaps[start+p:end+p]
        assert gaps[k-1] != gaps[k-1+p]
        assert all(any(gaps[k+i] != gaps[k+i+r] for i in range(p)) for r in range(1,p))
        assert seq[k+p]-seq[k] == modulus
        print(f"Table 1 {seeds}: k={k}, p={p}, m={modulus}; "
              f"first repeating block {gaps[k:k+p]}, four checked blocks.")
    print("All sequence entries agreed under both algorithms.")

if __name__ == "__main__":
    main()

