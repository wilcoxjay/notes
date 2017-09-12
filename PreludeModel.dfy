// RUN: /compile:0

module Sequence {
    datatype T<A> = Nil | Cons(head: T, tail: T<T>)

    function Length<A>(s: T<A>): int
    {
        match s
            case Nil => 0
            case Cons(_, s) => 1 + Length(s)
    }

    lemma lemma_LengthGe0<A>(s: T<A>)
        ensures 0 <= Length(s)
    {
        match s 
            case Nil => 
            case Cons(_, s) => lemma_LengthGe0(s);
    }
}

