module M {
    class C {
        var F: () -> ()

        function method CallF(): ()
            reads this, F.reads
            requires F.reads() == {}
            requires F.requires == (() => true)
        {
            F()
        }

    }

    method Main()
    {
        var c := new C;
        c.F := c.CallF;
        var x := c.CallF();
    }
}
