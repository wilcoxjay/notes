// RUN: /compile:0 /nologo /noNLarith /noCheating:1 /rlimit:1000000

module Spec {
    export reveals T, Behavior, BehaviorSatisfies
           provides ExtendBehavior

    datatype T<A> = Make(init: iset<A>, next: iset<(A, A)>)

    type Behavior<A> = seq<A>

    predicate BehaviorSatisfies<A>(b: Behavior<A>, spec: T<A>)
    {
        && |b| > 0 ==> b[0] in spec.init
        && forall i, j ::
            0 <= i < |b| - 1 && j == i + 1 ==> (b[i], b[j]) in spec.next
    }

    lemma ExtendBehavior<A>(spec: T<A>, b: Behavior<A>, a: A)
        requires |b| > 0 && BehaviorSatisfies(b, spec)
        requires (b[|b| - 1], a) in spec.next
        ensures  BehaviorSatisfies(b + [a], spec)
    {}
}


module Simulation {
    import Spec
    export reveals Request, InitDiagram, NextDiagram, ValidRequest
           provides Spec, PerformSimulation


    datatype Request<L, H> =
        Request(
          lspec: Spec.T<L>,
          hspec: Spec.T<H>,
          sim_rel: iset<(L, H)>
          )

    predicate InitDiagram<L, H>(req: Request<L, H>)
    {
        forall l :: l in req.lspec.init ==>
            exists h ::
                h in req.hspec.init && (l, h) in req.sim_rel
    }

    predicate NextDiagram<L, H>(req: Request<L, H>)
    {
        forall l, l', h ::
            && (l, l') in req.lspec.next
            && (l, h) in req.sim_rel
            ==> exists h' ::
                && (h, h') in req.hspec.next
                && (l', h') in req.sim_rel
    }

    predicate ValidRequest<L, H>(req: Request<L, H>)
    {
        && InitDiagram(req)
        && NextDiagram(req)
    }

    lemma PerformSimulation<L, H>(req: Request<L, H>, lb: Spec.Behavior<L>)
        returns (hb: Spec.Behavior<H>)
        requires ValidRequest(req)
        requires Spec.BehaviorSatisfies(lb, req.lspec)
        ensures |lb| == |hb|
        ensures Spec.BehaviorSatisfies(hb, req.hspec)
        ensures forall i :: 0 <= i < |lb| ==> (lb[i], hb[i]) in req.sim_rel
    {
        hb := [];
        while |hb| < |lb|
            invariant Spec.BehaviorSatisfies(hb, req.hspec)
            invariant 0 <= |hb| <= |lb|
            invariant forall i :: 0 <= i < |hb| ==> (lb[i], hb[i]) in req.sim_rel
        {
            var i := |hb| - 1;
            var h: H;
            if i == -1 {
                var h0 :| h0 in req.hspec.init && (lb[i+1], h0) in req.sim_rel;
                h := h0;
            } else {
                assert (lb[i], lb[i+1]) in req.lspec.next;
                var h' :| (hb[i], h') in req.hspec.next && (lb[i+1], h') in req.sim_rel;
                h := h';
            }
            hb := hb + [h];
        }
    }
}

module Invariants {
    import Spec
    export provides Spec, EstablishInvariantByInduction, InvariantTrueInitially
           reveals IsInvariant, IsInductive

    predicate IsInductive<A>(inv: iset<A>, spec: Spec.T<A>)
    {
        && spec.init <= inv
        && forall x, y ::
            && x in inv
            && (x, y) in spec.next
            ==> y in inv
    }

    predicate IsInductiveInReachable<A>(inv: iset<A>, spec: Spec.T<A>)
    {
        && spec.init <= inv
        && forall b, y ::
            && |b| > 0
            && Spec.BehaviorSatisfies(b, spec)
            && (var x := b[|b| - 1];
            && x in inv
            && (x, y) in spec.next)
            ==> y in inv
    }

    predicate IsInvariant<A>(inv: iset<A>, spec: Spec.T<A>)
    {
        forall b, i ::
            && Spec.BehaviorSatisfies(b, spec)
            && 0 <= i < |b|
            ==> b[i] in inv
    }

    lemma EstablishInvariantByInduction<A>(inv: iset<A>, spec: Spec.T<A>)
        requires IsInductive(inv, spec)
        ensures  IsInvariant(inv, spec)
    {
        forall b | Spec.BehaviorSatisfies(b, spec)
        ensures forall i :: 0 <= i < |b| ==> b[i] in inv
        {
            var j := 0;
            while j < |b|
                invariant 0 <= j <= |b|
                invariant forall i :: 0 <= i < j ==> b[i] in inv
            {
                if j != 0 {
                    assert (b[j-1], b[j]) in spec.next;
                }

                j := j + 1;
            }
        }
    }

    lemma EstablishInvariantByInductionInReachable<A>(inv: iset<A>, spec: Spec.T<A>)
        requires IsInductiveInReachable(inv, spec)
        ensures IsInvariant(inv, spec)
    {
        forall b | Spec.BehaviorSatisfies(b, spec)
        ensures forall i :: 0 <= i < |b| ==> b[i] in inv
        {
            var j := 0;
            while j < |b|
                invariant 0 <= j <= |b|
                invariant Spec.BehaviorSatisfies(b[..j], spec)
                invariant forall i :: 0 <= i < j ==> b[i] in inv
            {
                j := j + 1;
            }
        }
    }

    lemma InvariantImplies<A>(inv1: iset<A>, inv2: iset<A>, spec: Spec.T<A>)
        requires IsInvariant(inv1, spec)
        requires inv1 <= inv2
        ensures IsInvariant(inv2, spec)
    {}

    lemma InvariantTrueInitially<A>(inv: iset<A>, spec: Spec.T<A>)
        requires IsInvariant(inv, spec)
        ensures spec.init <= inv
    {
        forall x | x in spec.init
            ensures x in inv
        {
            var b := [x];
            assert Spec.BehaviorSatisfies(b, spec);
        }
    }

    function InvariantAndReachable<A>(inv: iset<A>, spec: Spec.T<A>): iset<A>
    {
        iset a: A, b |
            && a in inv
            && |b| > 0
            && Spec.BehaviorSatisfies(b, spec)
            && a == b[|b|-1]
        :: a
    }

    lemma InvariantAndReachableIsInvariant<A>(inv: iset<A>, spec: Spec.T<A>)
        requires IsInvariant(inv, spec)
        ensures IsInvariant(InvariantAndReachable(inv, spec), spec)
    {
        forall a | a in spec.init
            ensures a in InvariantAndReachable(inv, spec)
        {
            var b := [a];
            assert Spec.BehaviorSatisfies(b, spec) && b[0] in inv;
        }

        forall b, y |
            && |b| > 0
            && Spec.BehaviorSatisfies(b, spec)
            && (var x := b[|b| - 1];
            && x in InvariantAndReachable(inv, spec)
            && (x, y) in spec.next)
            ensures y in InvariantAndReachable(inv, spec)
        {
            var b' := b + [y];
            assert Spec.BehaviorSatisfies(b', spec) && b'[|b'| - 1] in inv;
        }

        EstablishInvariantByInductionInReachable(InvariantAndReachable(inv, spec), spec);
    }
}

module ConjoinInvariant {
    import Spec
    import Invariants
    import Simulation

    function ConjoinInvariantToInit<A>(init: iset<A>, inv: iset<A>): iset<A>
    {
        init * inv
    }

    function ConjoinInvariantToNext<A>(next: iset<(A, A)>, inv: iset<A>): iset<(A, A)>
    {
        iset a1, a2 | (a1, a2) in next && a1 in inv && a2 in inv :: (a1, a2)
    }

    function ConjoinInvariantToSpec<A>(spec: Spec.T<A>, inv: iset<A>): Spec.T<A>
    {
        Spec.Make(ConjoinInvariantToInit(spec.init, inv), ConjoinInvariantToNext(spec.next, inv))
    }

    function ConjoinInvariantSimulation<A>(spec: Spec.T<A>, inv: iset<A>): iset<(A, A)>
    {
        iset a, b |
            a in inv && Spec.BehaviorSatisfies(b, spec) && |b| > 0 && a == b[|b| - 1] :: (a, a)
    }

    function ConjoinInvariantRequest<A>(spec: Spec.T<A>, inv: iset<A>): Simulation.Request<A, A>
    {
        Simulation.Request(
            spec,
            ConjoinInvariantToSpec(spec, inv),
            ConjoinInvariantSimulation(spec, inv)
            )
    }

    lemma ConjoinInitSimulation<A>(spec: Spec.T<A>, inv: iset<A>)
        requires Invariants.IsInvariant(inv, spec)
        ensures (var req := ConjoinInvariantRequest(spec, inv);
            Simulation.InitDiagram(req))
    {
        var req := ConjoinInvariantRequest(spec, inv);
        forall l | l in req.lspec.init
            ensures exists h ::
                h in req.hspec.init && (l, h) in req.sim_rel
        {
            Invariants.InvariantTrueInitially(inv, spec);
            var b := [l];
            assert Spec.BehaviorSatisfies(b, spec);
            assert l in req.hspec.init && (l, l) in req.sim_rel;
        }

    }

    lemma ConjoinNextSimulation<A>(spec: Spec.T<A>, inv: iset<A>)
        requires Invariants.IsInvariant(inv, spec)
        ensures (var req := ConjoinInvariantRequest(spec, inv);
            Simulation.NextDiagram(req))
    {
        var req := ConjoinInvariantRequest(spec, inv);

        forall l, l', h |
            && (l, l') in req.lspec.next
            && (l, h) in req.sim_rel
        ensures
            && (h, l') in req.hspec.next
            && (l', l') in req.sim_rel
        {
            var b :| Spec.BehaviorSatisfies(b, spec) && |b| > 0 && l == b[|b| - 1];
            var b' := b + [l'];
            Spec.ExtendBehavior(spec, b, l');

            assert b'[|b'| - 1] in inv;
        }
    }


    lemma ConjoinInvariantToSpecSimulation<A>(spec: Spec.T<A>, inv: iset<A>)
        returns (req: Simulation.Request<A, A>)
        requires Invariants.IsInvariant(inv, spec)
        ensures req == ConjoinInvariantRequest(spec, inv)
        ensures Simulation.ValidRequest(req)
    {
        req := ConjoinInvariantRequest(spec, inv);

        ConjoinInitSimulation(spec, inv);
        ConjoinNextSimulation(spec, inv);
    }
}
