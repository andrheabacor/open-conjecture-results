"""Independent numerical checks for OEIS A179697, using only the standard library."""

from pathlib import Path


def direct(k: int) -> bool:
    """Evaluate the original two equations with string reversal."""
    def reverse(n: int) -> int:
        return int(format(n, "b")[::-1], 2)

    r = reverse(k)
    difference = abs(k - r)
    return abs(k + r - reverse(k + r)) == k == difference + reverse(difference)


def reverse_bits(number: int, width: int) -> int:
    result = 0
    for _ in range(width):
        result = (result << 1) | (number & 1)
        number >>= 1
    return result


def hamilton_crosscheck(published: list[int]) -> None:
    family_in_table = []
    for j in range(2, 1025):
        # Literal source word and string reversal of each original expression.
        word_member = int("10" + "1" * j + "010", 2)
        assert direct(word_member)

        # Independently construct k arithmetically and reverse by binary shifts.
        k = 6 * ((1 << (j + 2)) - 1)
        r = reverse_bits(k, k.bit_length())
        total = k + r
        difference = abs(k - r)
        assert abs(total - reverse_bits(total, total.bit_length())) == k
        assert difference + reverse_bits(difference, difference.bit_length()) == k
        assert k == word_member
        if k <= published[-1]:
            family_in_table.append(k)

    assert all(k in published for k in family_in_table)
    print("Hamilton's family checked independently by strings and integer shifts "
          "for every j from 2 through 1024.")
    print(f"All {len(family_in_table)} family members through {published[-1]} "
          "occur in the published table.")


def structural_terms(limit: int) -> list[int]:
    """Construct each possible palindrome from half its bits, then test 3q and 5q.

    This algorithm does not filter on the proposed prefix or suffix.
    """
    terms = []
    max_q = limit // 2
    for width in range(1, max_q.bit_length() + 1):
        half = (width + 1) // 2
        remaining = width // 2
        for head in range(1 << (half - 1), 1 << half):
            q = (head << remaining) | reverse_bits(head >> (width % 2), remaining)
            if q > max_q:
                break
            triple = 3 * q
            if reverse_bits(triple, triple.bit_length()) == 5 * q:
                terms.append(2 * q)
    return terms


def main() -> None:
    source = Path(__file__).with_name("b179697.txt")
    rows = [tuple(map(int, line.split())) for line in source.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    assert [row[0] for row in rows] == list(range(1, len(rows) + 1))
    published = [row[1] for row in rows]
    assert len(published) == 498
    assert direct(0)
    assert all(direct(k) for k in published)
    assert all(f"{k:b}".startswith("1011") and f"{k:b}".endswith("11010")
               for k in published)
    hamilton_crosscheck(published)

    exhaustive_limit = 2**18
    direct_terms = [k for k in range(1, exhaustive_limit + 1) if direct(k)]
    constructed = structural_terms(published[-1])
    assert direct_terms == [k for k in constructed if k <= exhaustive_limit]
    assert constructed == published
    print(f"Original equations checked directly for all {len(published)} OEIS terms.")
    print(f"Independent exhaustive comparison on 1..{exhaustive_limit}: "
          f"{len(direct_terms)} terms; the two lists agree.")
    print(f"Palindrome construction through {published[-1]}: "
          f"all {len(constructed)} terms agree with the published table in order.")
    print("All published terms have both ends. Zero satisfies the unrestricted equations.")


if __name__ == "__main__":
    main()
