module Spec {
    export reveals T, Behavior, BehaviorSatisfies

    datatype T<A> = Spec(init: iset<A>, next: iset<(A, A)>)

    type Behavior<A> = seq<A>

    predicate BehaviorSatisfies<A>(b: Behavior<A>, spec: T<A>)
    {
        && |b| > 0 ==> b[0] in spec.init
        && forall i :: 0 <= i < |b| - 1 ==> (b[i], b[i+1]) in spec.next
    }
}


module Simulation {
    import Spec
    export reveals Request, ValidRequest
           provides Spec, PerformSimulation
    

    datatype Request<L, H> = 
        Request(
          lspec: Spec.T<L>, 
          hspec: Spec.T<H>, 
          sim_rel: iset<(L, H)>
          )

    predicate ValidRequest<L, H>(req: Request<L, H>) 
    {
        && (forall l :: l in req.lspec.init ==> exists h :: h in req.hspec.init && (l, h) in req.sim_rel)
        && (forall l, l', h :: 
            && (l, l') in req.lspec.next 
            && (l, h) in req.sim_rel
            ==> exists h' :: 
                && (h, h') in req.hspec.next 
                && (l', h') in req.sim_rel)
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
                var h' :| (hb[i], h') in req.hspec.next && (lb[i+1], h') in req.sim_rel;
                h := h';
            }
            hb := hb + [h];
        }
    }
}

module Invariants {
    import Spec
    export provides Spec, IsInvariant, EstablishInvariant
           reveals IsInductive

    predicate IsInductive<A>(inv: iset<A>, spec: Spec.T<A>)
    {
        && spec.init <= inv
        && forall x, y :: 
            && x in inv 
            && (x, y) in spec.next
            ==> y in inv
    }

    predicate IsInvariant<A>(inv: iset<A>, spec: Spec.T<A>)
    {
        forall b, i :: 
            && Spec.BehaviorSatisfies(b, spec)
            && 0 <= i < |b|
            ==> b[i] in inv
    }

    lemma EstablishInvariant<A>(inv: iset<A>, spec: Spec.T<A>)
        requires IsInductive(inv, spec)
        ensures  IsInvariant(inv, spec)
    {
        forall b, i | 
            && Spec.BehaviorSatisfies(b, spec)
            && 0 <= i < |b|
        ensures b[i] in inv 
        {
            var j := 0;
            while j < i
                invariant 0 <= j <= i
                invariant b[j] in inv
            {
                j := j + 1;
            }
        }
    }
}

module ConjoinInvariant {
    import Spec
    import Invariants
    import Simulation

    function ConjoinInvariantToSpec<A>(spec: Spec.T<A>, inv: iset<A>): Spec.T<A>
    {
        spec
    }

    function ConjoinInvariantSimulation<A>(spec: Spec.T<A>, inv: iset<A>): iset<(A, A)>
    {
        iset a | a in inv :: (a, a)
    }

    function ConjoinInvariantRequest<A>(spec: Spec.T<A>, inv: iset<A>): Simulation.Request<A, A>
    {
        Simulation.Request(spec, ConjoinInvariantToSpec(spec, inv), ConjoinInvariantSimulation(spec, inv))
    }

    lemma ConjoinInvariantToSpecSimulation<A>(spec: Spec.T<A>, inv: iset<A>)
        returns (req: Simulation.Request<A, A>)
        requires Invariants.IsInvariant(inv, spec)
        ensures req == ConjoinInvariantRequest(spec, inv)
        ensures Simulation.ValidRequest(req)
    {
        req := ConjoinInvariantRequest(spec, inv);
        forall l | l in req.lspec.init 
            ensures exists h :: 
                && h in req.hspec.init
                && (l, h) in req.sim_rel
        {
            var b := [l];
            assert Spec.BehaviorSatisfies(b, spec);
            assert b[0] in inv;
        }
    }
}
