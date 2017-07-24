include "../armada/code/dafny/fl/spec/refinement.s.dfy"
include "../armada/code/dafny/fl/util/refinement/AnnotatedBehavior.i.dfy"
include "../armada/code/dafny/util/collections/seqs.i.dfy"

module TwoStateModule {
    import opened GeneralRefinementModule
    import opened AnnotatedBehaviorModule
    import opened util_collections_seqs_s
    import opened util_collections_seqs_i

    datatype PartiallyAnnotatedBehavior<S, A> =
        PartiallyAnnotatedBehavior(states: seq<S>, trace: seq<A>)

    datatype ActorTriple<S, T> = ActorTriple(s: S, s': S, actor: T)

    datatype YieldRequest<S(==), A(==), T(==)> = YieldPredicate(
        Y: iset<ActorTriple<S,T>>, 
        next: iset<ActionTriple<S,A>>,
        idmap: imap<A, T>, 
        pcs: seq<iset<StateActorPair<S,T>>>,
        pre: iset<StateActorPair<S,T>>,
        post: iset<StateActorPair<S,T>>
        )

    predicate YieldPredicateReflexive<S,T>(Y: iset<ActorTriple<S,T>>)
    {
        forall tid, s :: 
            ActorTriple(s, s, tid) in Y
    }

    predicate YieldPredicateTransitive<S,T>(Y: iset<ActorTriple<S,T>>)
    {
        forall tid, s1, s2, s3 :: 
            && ActorTriple(s1, s2, tid) in Y
            && ActorTriple(s2, s3, tid) in Y
            ==> ActorTriple(s1, s3, tid) in Y
    }

    predicate ActionTriplesHaveActors<S,A,T>(actions: iset<ActionTriple<S,A>>, idmap: imap<A, T>)
    {
        (iset a, s, s' | ActionTriple(s, s', a) in actions :: a) <= idmap.Keys
    }

    predicate YieldPredicateAbstractsInterference<S,A,T>(
        next: iset<ActionTriple<S,A>>, 
        Y: iset<ActorTriple<S,T>>,
        idmap: imap<A, T>
        )
    {
        forall a, tid, s, s' :: 
            && ActionTriple(s, s', a) in next
            && (a in idmap ==> idmap[a] != tid)
            ==> ActorTriple(s, s', tid) in Y
    }
    
    predicate StableUnderYield<S,T>(P: iset<StateActorPair<S,T>>, Y: iset<ActorTriple<S,T>>)
    {
        forall s, s', tid :: 
            ActorTriple(s, s', tid) in Y ==>
                (StateActorPair(s, tid) in P <==> StateActorPair(s', tid) in P)
    }

    // To be used once there is more than one statement
    predicate Consecutive<S,A,T>(
        pc1: iset<StateActorPair<S,T>>, 
        pc2: iset<StateActorPair<S,T>>, 
        next: iset<ActionTriple<S,A>>, 
        idmap: imap<A, T>
        )
    {
        forall a, tid, s, s' :: 
            && ActionTriple(s, s', a) in next
            && a in idmap 
            && idmap[a] == tid
            ==> (StateActorPair(s, tid) in pc1 <==> StateActorPair(s', tid) in pc2)
    }
    
    predicate AllActionsHaveActor<A,T>(idmap: imap<A, T>, trace: seq<A>, tid: T)
    {
        forall i :: 0 <= i < |trace| ==> trace[i] in idmap && idmap[trace[i]] == tid
    }

    predicate HoareLogicAssumptions<S,A,T>(
        r: YieldRequest<S, A, T>,
        their_states: seq<S>,
        my_states: seq<S>,
        trace: seq<A>)
    {
        && |their_states| == |my_states| == |r.pcs| == |trace| + 1
        && |trace| > 0
        && trace[0] in r.idmap 
        && var tid := r.idmap[trace[0]];
        && AllActionsHaveActor(r.idmap, trace, tid)
        && StateActorPair(their_states[0], tid) in r.pre
        && (forall i :: 0 <= i < |their_states| ==>
            ActorTriple(their_states[i], my_states[i], tid) in r.Y)
        && (forall i :: 0 <= i < |their_states| - 1 ==>
            ActionTriple(my_states[i], their_states[i+1], trace[i]) in r.next)
        && (forall i :: 0 <= i < |my_states| ==>
            StateActorPair(my_states[i], tid) in r.pcs[i])
    }

    predicate HoareLogic<S,A,T>(r: YieldRequest<S, A, T>)
    {
        forall their_states, my_states, trace ::
            HoareLogicAssumptions(r, their_states, my_states, trace)
            ==> StateActorPair(last(my_states), r.idmap[trace[0]]) in r.post
    }

    predicate ValidYieldRequest<S,A,T>(r: YieldRequest<S, A, T>)
    {
        && YieldPredicateReflexive(r.Y)
        && YieldPredicateTransitive(r.Y)
        && YieldPredicateAbstractsInterference(r.next, r.Y, r.idmap)
//        && (forall i :: 0 <= i < |r.pcs| ==> StableUnderYield(r.pcs[i], r.Y))
        && HoareLogic(r)
    }

    predicate RelyStateNextSeq<S,A,T>(
        next: iset<ActionTriple<S,A>>,
        idmap: imap<A, T>,
        states: seq<S>,
        trace: seq<A>,
        tid: T)
    {
        && StateNextSeq(states, trace, next)
        && (forall a' :: a' in trace && a' in idmap ==> idmap[a'] != tid)
    }

    predicate BehaviorLogicAssumptions<S, A, T>(
        r: YieldRequest<S, A, T>,
        bs: seq<PartiallyAnnotatedBehavior<S,A>>,
        trace: seq<A>)
    {
        && |bs| == |r.pcs| == |trace| + 1
        && |trace| > 0
        && trace[0] in r.idmap
        && var tid := r.idmap[trace[0]];
        && AllActionsHaveActor(r.idmap, trace, tid)
        && (forall i :: 0 <= i < |bs| ==>
            var PartiallyAnnotatedBehavior(s,t) := bs[i];
            && RelyStateNextSeq(r.next, r.idmap, s, t, tid)
            && StateActorPair(last(s), tid) in r.pcs[i])
        && StateActorPair(bs[0].states[0], tid) in r.pre
        && (forall i :: 0 <= i < |trace| ==>
            ActionTriple(last(bs[i].states), bs[i+1].states[0], trace[i]) in r.next)
    }

    predicate BehaviorLogic<S, A, T>(r: YieldRequest<S, A, T>)
    {
        forall bs, trace ::
            BehaviorLogicAssumptions(r, bs, trace)
            ==> StateActorPair(last(last(bs).states), r.idmap[trace[0]]) in r.post
    }

    lemma lemma_UseHoareLogic<S,A,T>(
        r: YieldRequest<S, A, T>,
        their_states: seq<S>,
        my_states: seq<S>,
        trace: seq<A>
        )
        requires HoareLogic(r)
        requires HoareLogicAssumptions(r, their_states, my_states, trace)
        ensures StateActorPair(last(my_states), r.idmap[trace[0]]) in r.post
    {}

    lemma lemma_YieldAbstractsNextSequence<S,A,T>(
        next: iset<ActionTriple<S,A>>,
        Y: iset<ActorTriple<S,T>>, 
        idmap: imap<A, T>, 
        states: seq<S>, 
        trace: seq<A>,
        tid: T
        )
        requires YieldPredicateReflexive(Y)
        requires YieldPredicateTransitive(Y)
        requires YieldPredicateAbstractsInterference(next, Y, idmap)
        requires RelyStateNextSeq(next, idmap, states, trace, tid)
        ensures ActorTriple(states[0], last(states), tid) in Y
    {
        var i := 0;
        while i < |states| - 1
            invariant 0 <= i <= |states| - 1
            invariant ActorTriple(states[0], states[i], tid) in Y
        {
            assert ActionTriple(states[i], states[i+1], trace[i]) in next;
            assert ActorTriple(states[i], states[i+1], tid) in Y;
            i := i + 1;
        }

    }

    lemma lemma_UseYieldPredicate<S,A,T>(
        r: YieldRequest<S, A, T>,
        bs: seq<PartiallyAnnotatedBehavior<S,A>>,
        trace: seq<A>
        )
        requires ValidYieldRequest(r)
        requires BehaviorLogicAssumptions(r, bs, trace)
        ensures StateActorPair(last(last(bs).states), r.idmap[trace[0]]) in r.post
    {
        var tid := r.idmap[trace[0]];

        forall i | 0 <= i < |bs|
            ensures ActorTriple(bs[i].states[0], last(bs[i].states), tid) in r.Y
        {
            var s := bs[i].states;
            var t := bs[i].trace;
            lemma_YieldAbstractsNextSequence(r.next, r.Y, r.idmap, s, t, tid);
        }

        var their_states := ConvertMapToSeq(|bs|, map i | 0 <= i < |bs| :: bs[i].states[0]);
        var my_states := ConvertMapToSeq(|bs|, map i | 0 <= i < |bs| :: last(bs[i].states));

        lemma_UseHoareLogic(r, their_states, my_states, trace);
    }

    function AppendCompatiblePB<S, A>(
        pb1: PartiallyAnnotatedBehavior<S, A>,
        pb2: PartiallyAnnotatedBehavior<S, A>
        ):
        PartiallyAnnotatedBehavior<S, A>
        // requires |pb2.states| > 0
        // requires last(pb1.states) == pb2.states[0]
    {
        if pb2.states != [] then
            PartiallyAnnotatedBehavior(pb1.states + pb2.states[1..], pb1.trace + pb2.trace)
        else
            pb1
    }

    function AppendPBWithIntermediateAction<S, A>(
        pb1: PartiallyAnnotatedBehavior<S, A>,
        a: A,
        pb2: PartiallyAnnotatedBehavior<S, A>
        ):
        PartiallyAnnotatedBehavior<S, A>
    {
        PartiallyAnnotatedBehavior(pb1.states + pb2.states, pb1.trace + [a] + pb2.trace)
    }

    function ConcatPBWithIntermediateTrace<S, A>(
        pbs: seq<PartiallyAnnotatedBehavior<S, A>>,
        trace: seq<A>
        ):
        PartiallyAnnotatedBehavior<S, A>
        requires |pbs| == |trace| + 1
    {
        if trace == [] then
            pbs[0]
        else
            var rest := ConcatPBWithIntermediateTrace(pbs[1..], trace[1..]);
            AppendPBWithIntermediateAction(pbs[0], trace[0], rest)
    }


    lemma lemma_FactorOutThreadActions<S,A,T>(
        r: YieldRequest<S, A, T>,
        b: PartiallyAnnotatedBehavior<S, A>,
        tid: T
        ) returns (
        prefix: PartiallyAnnotatedBehavior<S,A>,
        bs: seq<PartiallyAnnotatedBehavior<S,A>>,
        trace: seq<A>,
        suffix: PartiallyAnnotatedBehavior<S,A>
        )
        requires ValidYieldRequest(r)
        requires StateNextSeq(b.states, b.trace, r.next)

        ensures |bs| == |trace| + 1
        ensures var middle := ConcatPBWithIntermediateTrace(bs, trace);
            AppendCompatiblePB(prefix, AppendCompatiblePB(middle, suffix)) == b

        ensures StateNextSeq(prefix.states, prefix.trace, r.next)
        ensures BehaviorLogicAssumptions(r, bs, trace)
        ensures StateNextSeq(suffix.states, suffix.trace, r.next)

        ensures last(prefix.states) == bs[0].states[0]
        ensures last(last(bs).states) == suffix.states[0]
    {
    }

}
