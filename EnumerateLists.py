import itertools

def product(A, Bf):
    in_progress = []

    while True:
        try:
            a = A.next()
            in_progress.append((a, Bf()))
        except StopIteration:
            pass

        for (a, B) in in_progress:
            try:
                b = B.next()
                yield (a, b)
            except StopIteration:
                pass

def ints():
    n = 0
    while True:
        yield n
        n = -n
        if n >= 0:
            n += 1

def evens():
    n = 0
    while True:
        yield n
        n += 2


def odds():
    n = 1
    while True:
        yield n
        n += 2

def unit():
    yield ()

def n_tuple_aux(n, Af):
    if n == 0:
        return unit()
    else:
        return product(n_tuple_aux(n-1, Af), Af)

def n_tuple(n, Af):
    for t in n_tuple_aux(n, Af):
        l = []
        for i in range(n):
            l.append(t[1])
            t = t[0]
        l.reverse()
        yield tuple(l)

def lists(Af):
    in_progress = []
    n = 0

    while True:
        in_progress.append((n, n_tuple(n, Af)))
        n += 1
        for (d, i) in in_progress:
            for _ in range(n * (n - d)):
                try:
                    yield list(i.next())
                except StopIteration:
                    pass


def main():
    count = 0
    for l in lists(ints):
        if l == [1, 2, 3, 4]:
            break
        count += 1

    print count
