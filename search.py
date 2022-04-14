from typing import Sequence


def linear_search(needle: int, haystack: Sequence[int]) -> bool:
    for i, x in enumerate(haystack):
        if x == needle:
            return True

    return False

linear_search(11, [2, 11, 7, 5])
linear_search(10 ** 6, range(10 ** 9))

def binary_search(needle: int, haystack: Sequence[int]) -> bool:
    """Search for needle in *sorted* haystack. Return index of first occurrence, or -1 if not found."""

    # We repeatedly narrow the interval where needle might be, represented by lo...hi
    # (including lo, excluding hi, as is standard in python).

    # Initially the interval is the whole array.
    lo = 0
    hi = len(haystack)

    # Invariant: if needle is in the haystack, it is in the interval lo...hi
    while lo < hi:
        middle = (lo + hi) // 2
        candidate = haystack[middle]

        if candidate == needle:
            return True
        elif candidate < needle:
            lo = middle + 1  # "fun" exercise: what happens without +1 here?
        else:
            hi = middle

    return False

binary_search(11, [2, 11, 7, 5])  # bogus! input must be sorted (not a bug in binary_search impl :))
binary_search(11, [2, 5, 7, 11])
binary_search(10 ** 6, range(10 ** 9))
binary_search(10 ** 8, range(10 ** 9))
binary_search(10 ** 16, range(10 ** 18))
binary_search(10 ** 9 + 1, range(0, 10 ** 18, 2))

# "fun" blog post: Nearly All Binary Searches are Broken
#
#     https://ai.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html
#
# short version: in languages with bounded integers, the line "(lo + hi) // 2" can overflow
