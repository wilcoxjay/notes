module M1 {
    import M2

    function even(n: nat): bool
        decreases n
    {
        if n == 0 then
            true
        else
            M2.odd(n - 1, (x: nat) requires x < n => even(x))
    }
}


module M2 {
    function odd(n: nat, f: nat -> bool): bool
        reads f.reads
        requires forall x: nat :: x < n ==> f.requires(x)
    {
        if n == 0 then
            false
        else
            f(n - 1)
    }
}


