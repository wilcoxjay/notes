// RUN: /compile:0

module M {
    export provides C

    class C {
        constructor() {
        }
    }
}

module Main {
    import M

    method Main() {
        var x := new M.C();
    }
}
