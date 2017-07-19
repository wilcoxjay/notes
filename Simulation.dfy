// RUN: /compile:0 /nologo /noNLarith /noCheating:1 /rlimit:1000000

module OptionModule {
    datatype Option<A> = None | Some(val: A)
}

module SetModule {
    export reveals AllElements

    function AllElements<A>(): iset<A> 
    {
        iset a: A | true
    }
}

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
    import Invariants
    export reveals Request, InitDiagram, NextDiagram, ValidRequest
           provides Spec, Invariants, PerformSimulation


    datatype Request<L, H> =
        Request(
          lspec: Spec.T<L>,
          hspec: Spec.T<H>,
          inv: iset<L>,
          sim_rel: iset<(L, H)>
          )

    predicate InitDiagram<L, H>(req: Request<L, H>)
    {
        forall l :: 
            && l in req.lspec.init
            && l in req.inv
            ==>
            exists h ::
                h in req.hspec.init && (l, h) in req.sim_rel
    }

    predicate NextDiagram<L, H>(req: Request<L, H>)
    {
        forall l, l', h ::
            && (l, l') in req.lspec.next
            && (l, h) in req.sim_rel
            && l in req.inv
            ==> exists h' ::
                && (h, h') in req.hspec.next
                && (l', h') in req.sim_rel
    }

    predicate ValidRequest<L, H>(req: Request<L, H>)
    {
        && Invariants.IsInvariant(req.inv, req.lspec)
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
    export provides Spec, EstablishInvariantByInduction, InvariantTrueInitially, InvariantImplies
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

module Example {
    module Layer0 {
        import Spec 

        type Tid = int

        datatype State = State(b: bool)
            
        predicate Init(s: State)
        {
            !s.b
        }

        predicate Acquire(tid: Tid, s: State, s': State) 
        {
            && !s.b
            && s'.b
        }

        predicate Release(tid: Tid, s: State, s': State) 
        {
            && s.b
            && !s'.b
        }

        predicate ThreadNext(tid: Tid, s: State, s': State)
        {
            || Acquire(tid, s, s')
            || Release(tid, s, s')
        }

        predicate Next(s: State, s': State)
        {
            exists tid :: ThreadNext(tid, s, s')
        }

        function GetSpec(): Spec.T<State>
        {
            Spec.Make(iset s | Init(s), iset s1, s2 | Next(s1, s2) :: (s1, s2))
        }
    }

    module Layer1 {
        import Spec
        import Invariants
        import opened OptionModule

        type Tid = int

        datatype State = State(b: bool, lock: Option<Tid>)
            
        predicate Init(s: State)
        {
            && !s.b
            && s.lock.None?
        }

        predicate Acquire(tid: Tid, s: State, s': State) 
        {
            && !s.b
            && s'.b
            && s'.lock == Some(tid)
        }

        predicate Release(tid: Tid, s: State, s': State) 
        {
            && s.b
            && !s'.b
            && s'.lock.None?
        }

        predicate ThreadNext(tid: Tid, s: State, s': State)
        {
            || Acquire(tid, s, s')
            || Release(tid, s, s')
        }

        predicate Next(s: State, s': State)
        {
            exists tid :: ThreadNext(tid, s, s')
        }

        function GetSpec(): Spec.T<State>
        {
            Spec.Make(iset s | Init(s), iset s1, s2 | Next(s1, s2) :: (s1, s2))
        }

        predicate Inv(s: State)
        {
            s.b <==> s.lock.Some?
        }

        function GetInv(): iset<State>
        {
            iset s | Inv(s)
        }

        lemma InvIsInvariant()
            ensures Invariants.IsInvariant(GetInv(), GetSpec())
        {
            Invariants.EstablishInvariantByInduction(GetInv(), GetSpec());
        }
    }

    module Layer2 {
        import Spec
        import opened OptionModule

        type Tid = int

        datatype State = State(lock: Option<Tid>)
            
        predicate Init(s: State)
        {
            s.lock.None?
        }

        predicate Acquire(tid: Tid, s: State, s': State) 
        {
            && s.lock.None?
            && s'.lock == Some(tid)
        }

        predicate Release(tid: Tid, s: State, s': State) 
        {
            && s.lock.Some?
            && s'.lock.None?
        }

        predicate ThreadNext(tid: Tid, s: State, s': State)
        {
            || Acquire(tid, s, s')
            || Release(tid, s, s')
        }

        predicate Next(s: State, s': State)
        {
            exists tid :: ThreadNext(tid, s, s')
        }

        function GetSpec(): Spec.T<State>
        {
            Spec.Make(iset s | Init(s), iset s1, s2 | Next(s1, s2) :: (s1, s2))
        }
    }

    module Sim01 {
        import Low = Layer0
        import High = Layer1
        import Spec
        import Simulation
        import opened OptionModule
        import opened SetModule

        predicate SimRel(s0: Low.State, s1: High.State) 
        {
            s0.b == s1.b
        }

        function GetRequest(): Simulation.Request<Low.State, High.State>
        {
            Simulation.Request(Low.GetSpec(), High.GetSpec(), AllElements(), iset s0, s1 | SimRel(s0, s1) :: (s0, s1))
        }

        lemma InitDiagram()
            ensures Simulation.InitDiagram(GetRequest())
        {
            var req := GetRequest();
            forall l | l in req.lspec.init 
                ensures var h := High.State(false, None); h in req.hspec.init && (l, h) in req.sim_rel
            {
            }
        }

        lemma NextDiagram()
            ensures Simulation.NextDiagram(GetRequest())
        {
            var req := GetRequest();
            forall l, l', h |
                && (l, l') in req.lspec.next
                && (l, h) in req.sim_rel
            ensures exists h' ::
                    && (h, h') in req.hspec.next
                    && (l', h') in req.sim_rel
            {
                var tid :| Low.ThreadNext(tid, l, l');
                var h': High.State;
                if Low.Acquire(tid, l, l') {
                    h' := High.State(l'.b, Some(tid));
                } else {
                    assert Low.Release(tid, l, l');
                    h' := High.State(l'.b, None);
                }
                assert High.ThreadNext(tid, h, h');
                assert (h, h') in req.hspec.next;
            }
        }

        lemma Sim()
            ensures Simulation.ValidRequest(GetRequest())
        {
            var req := GetRequest();
            InitDiagram();
            NextDiagram();
        }
    }

    module Sim12 {
        import Low = Layer1
        import High = Layer2
        import Spec
        import Simulation
        import opened OptionModule
        import opened SetModule

        predicate SimRel(s1: Low.State, s2: High.State) 
        {
            && s1.lock == s2.lock
        }

        function GetRequest(): Simulation.Request<Low.State, High.State>
        {
            Simulation.Request(Low.GetSpec(), High.GetSpec(), Low.GetInv(), iset s0, s1 | SimRel(s0, s1) :: (s0, s1))
        }

        lemma InitDiagram()
            ensures Simulation.InitDiagram(GetRequest())
        {
            var req := GetRequest();
            forall l | l in req.lspec.init 
                ensures var h := High.State(None); h in req.hspec.init && (l, h) in req.sim_rel
            {
            }
        }

        lemma NextDiagram()
            ensures Simulation.NextDiagram(GetRequest())
        {
            var req := GetRequest();
            forall l, l', h |
                && (l, l') in req.lspec.next
                && (l, h) in req.sim_rel
                && Low.Inv(l)
            ensures exists h' ::
                    && (h, h') in req.hspec.next
                    && (l', h') in req.sim_rel
            {
                var tid :| Low.ThreadNext(tid, l, l');
                var h' := High.State(l'.lock);
                assert High.ThreadNext(tid, h, h');
                assert (h, h') in req.hspec.next;
            }
        }

        lemma Sim()
            ensures Simulation.ValidRequest(GetRequest())
        {
            var req := GetRequest();
            Low.InvIsInvariant();
            InitDiagram();
            NextDiagram();
        }
    }
}
