from z3 import *

# this is not used below, it's just here as documentation
def dijkstra(a, b, c):
    if a == 0:
        return c
    elif a % 2 == 0:
        return dijkstra(a // 2, b * 2, c)
    else:
        return dijkstra(a - 1, b, c + b)

def main():

    B = BoolSort()
    Z = IntSort()
    s = SolverFor('HORN')

    # relational encoding of dijkstra function
    DIJKSTRA = Function('DIJKSTRA', Z, Z, Z, Z, B)
    a, b, c, d = Ints('a b c d')

    # Now add three constraints that are read off from the function definition.
    s.add(ForAll([a, b, c], Implies(a == IntVal(0), DIJKSTRA(a, b, c, c))))
    s.add(ForAll([a, b, c, d], Implies(And(a != IntVal(0),
                                           a % IntVal(2) == IntVal(0),
                                           DIJKSTRA(a / IntVal(2), b * IntVal(2), c, d)),
                                       DIJKSTRA(a, b, c, d))))
    s.add(ForAll([a, b, c, d], Implies(And(a != IntVal(0),
                                           a % IntVal(2) == IntVal(1),
                                           DIJKSTRA(a - IntVal(1), b, c + b, d)),
                                       DIJKSTRA(a, b, c, d))))

    # Now add the desired specification, that it returns a * b + c
    s.add(ForAll([a, b, c, d], Implies(DIJKSTRA(a, b, c, d), d == a * b + c)))

    # In principle, this should come back SAT in such a way that we can read
    # out an inductive invariant.
    print(s.check())
