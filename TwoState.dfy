include "../armada/code/dafny/fl/spec/refinement.s.dfy"
include "../armada/code/dafny/fl/util/refinement/AnnotatedBehavior.i.dfy"

module TwoStateModule {
    import opened GeneralRefinementModule
    import opened AnnotatedBehaviorModule
    import opened util_collections_seqs_s

    datatype ActorTriple<S, T> = ActorTriple(s: S, s': S, actor: T)

    datatype YieldRequest<S(==), A(==), T(==)> = YieldPredicate(
        Y: iset<ActorTriple<S,T>>, 
        next: iset<ActionTriple<S,A>>,
        idmap: imap<A, T>, 
        pc: iset<StateActorPair<S,T>>,
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
            ActorTriple(s, s', tid) in Y ==> (StateActorPair(s, tid) in P <==> StateActorPair(s', tid) in P)
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
    
    predicate HoareLogicAssumptions<S,A,T>(r: YieldRequest<S, A, T>, s0: S, s1: S, s2: S, s3: S, a: A)
    {
        && a in r.idmap 
        && var tid := r.idmap[a];
        && StateActorPair(s0, tid) in r.pre
        && ActorTriple(s0, s1, tid) in r.Y
        && StateActorPair(s1, tid) in r.pc
        && ActionTriple(s1, s2, a) in r.next
        && ActorTriple(s2, s3, tid) in r.Y

    }

    predicate HoareLogic<S,A,T>(r: YieldRequest<S, A, T>)
    {
        forall s0, s1, s2, s3, a :: 
            HoareLogicAssumptions(r, s0, s1, s2, s3, a)
            ==> StateActorPair(s3, r.idmap[a]) in r.post
    }

    predicate ValidYieldRequest<S,A,T>(r: YieldRequest<S, A, T>)
    {
        && YieldPredicateReflexive(r.Y)
        && YieldPredicateTransitive(r.Y)
        && YieldPredicateAbstractsInterference(r.next, r.Y, r.idmap)
        && StableUnderYield(r.pc, r.Y)
        && HoareLogic(r)
    }

    predicate RelyStateNextSeq<S,A,T>(next: iset<ActionTriple<S,A>>, idmap: imap<A, T>, states: seq<S>, trace: seq<A>, tid: T)
    {
        && StateNextSeq(states, trace, next)
        && (forall a' :: a' in trace && a' in idmap ==> idmap[a'] != tid)
    }

    predicate BehaviorLogicAssumptions<S, A, T>(r: YieldRequest<S, A, T>, states0: seq<S>, trace0: seq<A>, states1: seq<S>, trace1: seq<A>, a: A)
    {
        && a in r.idmap 
        && var tid := r.idmap[a]; 
        && RelyStateNextSeq(r.next, r.idmap, states0, trace0, tid)
        && RelyStateNextSeq(r.next, r.idmap, states1, trace1, tid)
        && StateActorPair(states0[0], tid) in r.pre
        && StateActorPair(last(states0), tid) in r.pc
        && ActionTriple(last(states0), states1[0], a) in r.next
    }

    predicate BehaviorLogic<S, A, T>(r: YieldRequest<S, A, T>)
    {
        forall states0, trace0, states1, trace1, a :: 
            BehaviorLogicAssumptions(r, states0, trace0, states1, trace1, a)
            ==> StateActorPair(last(states1), r.idmap[a]) in r.post
    }

    lemma lemma_UseHoareLogic<S,A,T>(r: YieldRequest<S, A, T>, s0: S, s1: S, s2: S, s3: S, a: A)
        requires HoareLogic(r)
        requires HoareLogicAssumptions(r, s0, s1, s2, s3, a)
        ensures StateActorPair(s3, r.idmap[a]) in r.post
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
        states0: seq<S>, 
        trace0: seq<A>, 
        states1: seq<S>, 
        trace1: seq<A>, 
        a: A
        )
        requires ValidYieldRequest(r)
        requires BehaviorLogicAssumptions(r, states0, trace0, states1, trace1, a)
        ensures StateActorPair(last(states1), r.idmap[a]) in r.post
    {
        var tid := r.idmap[a];
        var s0 := states0[0];
        var s1 := last(states0);
        var s2 := states1[0];
        var s3 := last(states1);

        lemma_YieldAbstractsNextSequence(r.next, r.Y, r.idmap, states0, trace0, tid);
        lemma_YieldAbstractsNextSequence(r.next, r.Y, r.idmap, states1, trace1, tid);
        lemma_UseHoareLogic(r, s0, s1, s2, s3, a);
    }
}
