from typing import Callable, Iterator, cast, TypeVar
from typing_extensions import Protocol

T = TypeVar('T')

class FakeArray:
    def __init__(self, f: Callable[[int], int]) -> None:
        self.f = f

    def __getitem__(self, i: int) -> int:
        return self.f(i)

    def __iter__(self) -> Iterator[int]:
        i = 0
        while True:
            yield self.f(i)
            i += 1

# positive_integers = cast(List[int], FakeArray(lambda i: i))
