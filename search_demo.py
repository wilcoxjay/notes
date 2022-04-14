from typing import Sequence


def linear_search(needle: int, haystack: Sequence[int]) -> bool:
    for i, x in enumerate(haystack):
        if x == needle:
            return True

    return False

# haystack must be sorted!
def binary_search(needle: int, haystack: Sequence[int]) -> bool:
    # interval is represented as lo...hi, indices i where lo <= i < hi
    lo = 0
    hi = len(haystack)

    while lo != hi:
        # make a guess
        midpoint = (lo + hi) // 2
        guess = haystack[midpoint]
        # refine the guess
        if guess == needle:
            return True
        elif guess > needle:
            # go left
            hi = midpoint
        else:  # guess < needle
            # go right
            lo = midpoint + 1
    return False
