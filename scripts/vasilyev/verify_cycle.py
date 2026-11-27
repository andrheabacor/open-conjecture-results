"""Independent reproduction via affine bounds on complete direction words.

Standard library only. Reads the written vertex certificate to compare against
the orbit reconstructed solely from a fixed 233-letter word.
"""
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).parent
WITNESS_WORD = (
    "UUUUUUUDUUUUUDUDUDUUUUUDDUUDDUUDDUUDUDDDUUUUUDUU"
    "UUUUDDUUUDUDUUDUDUDUUDUUDUUUUDUUDUDUUDDUUDDUUUUU"
    "DUDUUDDDDUDUUDUUUUUUUDUUDUDDUUUDDUUDUUUDUUUDDUDU"
    "DUUUUUDUDUUDDUUDUUDDUUDUDDUDUDUDDUUUDUUUUUUUUUDU"
    "UDUDUDUDUUDDUUDUUDUUUUDUDUUDUDDUDUDDDDUDD"
)


def fixed_positive_starts(word):
    """Enumerate all admissible starts, with no prescribed ceiling on vertices."""
    denominator = 2 ** len(word)
    slope = 1
    max_offset = 0
    for i, letter in enumerate(word):
        m = 3 if letter == "U" else 1
        slope *= m
        max_offset = m * max_offset + 2**i
    if slope >= denominator:
        return
    for start in range(1, 1 + max_offset // (denominator - slope)):
        orbit = []
        x = start
        for letter in word:
            orbit.append(x)
            factor = 3 if letter == "U" else 1
            # Independent ceiling identity for an odd multiplier:
            # ceil(m*x/2) = floor(m*x/2) + (x mod 2).
            x = factor*x//2 + (x & 1)
        if x == start:
            yield orbit


def is_simple_and_canonical(orbit):
    return orbit[0] == min(orbit) and len(orbit) == len(set(orbit))


def census(length):
    cycles = []
    for word in itertools.product("DU",repeat=length):
        for orbit in fixed_positive_starts(word):
            if is_simple_and_canonical(orbit):
                cycles.append((tuple(orbit),word.count("U")))
    assert len(cycles) == len(set(cycles))
    if not cycles:
        return (0,0,[])
    return len(cycles),max(max(orbit) for orbit,_ in cycles), sorted({ups for _,ups in cycles})


def verify():
    # The following values come from Vasilyev v2, Table 4.1.
    for length, expected in [(1,(1,1,[0])), (2,(3,5,[1])), (3,(0,0,[])),
                              (4,(0,0,[])), (5,(12,26,[3])), (8,(140,242,[5])),
                              (10,(18,41,[6]))]:
        actual = census(length)
        assert actual == expected,(length,actual)
        print(f"length {length}: {actual[0]} cycles, maximum {actual[1]}, up counts {actual[2]}")
    written = json.loads((ROOT / "cycle.json").read_text(encoding="utf-8"))
    recovered = [v for v in fixed_positive_starts(WITNESS_WORD) if is_simple_and_canonical(v)]
    assert written in recovered and written[0]==3
    # Work backwards through the edges using the defining ceiling inequality.
    # This checks branch choices without evaluating a ceiling.
    ascents=0
    for x,y in zip(written,written[1:]+written[:1]):
        matches = [m for m in (1,3) if 2*y-2 < m*x <= 2*y]
        assert len(matches)==1
        ascents += matches[0]==3
    length = len(written)
    assert (length,ascents,max(written)) == (233,146,698)
    assert WITNESS_WORD.count("U")==ascents and 2**length > 3**(ascents+1)
    print("Direction-word fixed points with a simple cycle in least-first order:", [v[0] for v in recovered])
    print("Complete reconstructed orbit equals cycle.json.")
    print("Length, up, down, min, max:",length,ascents,length-ascents,min(written),max(written))
    print("2^233 - 3^147 =",2**length-3**(ascents+1))


if __name__ == "__main__":
    verify()

