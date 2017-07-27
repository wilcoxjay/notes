include "CivlizedMathPrelude.dfy"
include "../../fl/spec/refinement.s.dfy"
include "../../fl/util/simulation.i.dfy"
include "../../fl/util/refinement/AnnotatedBehavior.i.dfy"

module ProducerConsumerConfig {
    datatype Config = Config
}

module ProducerConsumerAction {
    datatype Action = InputAction | OutputAction
}


module ProducerConsumer {
    import opened util_option_s
    import opened Prelude
    import opened GeneralRefinementModule
    import opened ProducerConsumerAction

    datatype SharedState = SharedState(buffer: Option<int>)

    datatype MainPC = MainPC0 | MainPC1 | MainPC2
    datatype ProducerPC = ProducerPC0 | ProducerPC1 
    datatype ConsumerPC = ConsumerPC0 | ConsumerPC1 

    datatype MainState = MainState
    datatype ProducerState = ProducerState(x: int)
    datatype ConsumerState = ConsumerState(x: int)

    datatype ThreadState = MainThread(mainpc: MainPC, mainstate: MainState)
                         | ProducerThread(producerpc: ProducerPC, producerstate: ProducerState)
                         | ConsumerThread(consumerpc: ConsumerPC, consumerstate: ConsumerState)

    type State = TotalState<SharedState, ThreadState>


    function ProducerInitSet(): iset<ThreadState>
    {
        iset ts: ThreadState | ts.ProducerThread? && ts.producerpc == ProducerPC0
    }

    function ConsumerInitSet(): iset<ThreadState>
    {
        iset ts: ThreadState | ts.ConsumerThread? && ts.consumerpc == ConsumerPC0
    }

    function MainInitSet(): iset<ThreadState>
    {
        iset ts: ThreadState | ts.MainThread? && ts.mainpc == MainPC0
    }

    predicate SharedInit(s: SharedState)
    {
        s.buffer.None?
    }

    predicate Init(s: State) 
    {
        && SharedInit(s.shared)
        && s.external == []
        && exists main_tid :: 
            && s.locals.Keys == {main_tid}
            && s.locals[main_tid].Some?
            && s.locals[main_tid].v in MainInitSet()
    }

    predicate Produce(tid: Tid, s: State, s': State, x: int)
    {
        && s.shared.buffer.None?
        && s'.shared.buffer == Some(x)
    }

    predicate Consume(tid: Tid, s: State, s': State, x: int)
    {
        && s.shared.buffer.Some?
        && x == s.shared.buffer.v
        && s'.shared.buffer.None?
    }

    predicate ProducerNext(tid: Tid, s: State, s': State)
        requires tid in s.locals && s.locals[tid].Some? && s.locals[tid].v.ProducerThread? && s.locals.Keys <= s'.locals.Keys
    {
        match s.locals[tid].v.producerpc
            case ProducerPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ProducerThread?
                && Input(tid, s, s', s'.locals[tid].v.producerstate.x)
                && s'.locals[tid].v.producerpc == ProducerPC1
            case ProducerPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ProducerThread?
                && Produce(tid, s, s', s.locals[tid].v.producerstate.x)
                && s'.locals[tid].v.producerpc == ProducerPC0
    }

    predicate ConsumerNext(tid: Tid, s: State, s': State)
        requires tid in s.locals && s.locals[tid].Some? && s.locals[tid].v.ConsumerThread? && s.locals.Keys <= s'.locals.Keys
    {
        match s.locals[tid].v.consumerpc
            case ConsumerPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ConsumerThread?
                && Consume(tid, s, s', s'.locals[tid].v.consumerstate.x)
                && s'.locals[tid].v.consumerpc == ConsumerPC1
            case ConsumerPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ConsumerThread?
                && Output(tid, s, s', s.locals[tid].v.consumerstate.x)
                && s'.locals[tid].v.consumerpc == ConsumerPC0
    }

    predicate MainNext(tid: Tid, s: State, s': State)
        requires tid in s.locals && s.locals[tid].Some? && s.locals[tid].v.MainThread? && s.locals.Keys <= s'.locals.Keys
    {
        match s.locals[tid].v.mainpc
            case MainPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && (exists tid' :: Fork(tid, s, s', ProducerInitSet(), tid'))
                && s'.locals[tid].v.mainpc == MainPC1
            case MainPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && (exists tid' :: Fork(tid, s, s', ConsumerInitSet(), tid'))
                && s'.locals[tid].v.mainpc == MainPC2
            case MainPC2 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && Nop(tid, s, s')
                && s'.locals[tid].v.mainpc == MainPC2
    }

    predicate ThreadNext(tid: Tid, s: State, s': State)
    {
        && tid in s.locals
        && s.locals[tid].Some?
        && s.locals.Keys <= s'.locals.Keys
        && (forall tid' :: tid' != tid && tid' in s.locals ==> s'.locals[tid'] == s.locals[tid'])
        && match s.locals[tid].v
            case MainThread(_,_) => MainNext(tid, s, s')
            case ProducerThread(_, _) => ProducerNext(tid, s, s')
            case ConsumerThread(_, _) => ConsumerNext(tid, s, s')
    }

    predicate Next(s: State, s': State)
    {
        exists tid :: ThreadNext(tid, s, s')
    }

    function GetSpec(): Spec<State>
    {
        Spec(iset s | Init(s), iset s, s' | Next(s, s') :: StatePair(s, s'))
    }
}

module ProducerConsumerSpec {
    import opened Prelude
    import opened GeneralRefinementModule
    import opened ProducerConsumerConfig
    import opened AnnotatedBehaviorModule
    import opened ProducerConsumerAction

    datatype SharedState = SharedState

    datatype MainPC = MainPC0 | MainPC1 
    datatype MainState = MainState(x: int)

    datatype ThreadState = MainThread(mainpc: MainPC, mainstate: MainState)

    type State = TotalState<SharedState, ThreadState>

    function MainInitSet(): iset<ThreadState>
    {
        iset ts: ThreadState | ts.MainThread? && ts.mainpc == MainPC0
    }

    predicate SharedInit(s: SharedState)
    {
        true
    }

    predicate Init(s: State) 
    {
        && SharedInit(s.shared)
        && s.external == []
        && exists main_tid :: 
            && s.locals.Keys == {main_tid}
            && s.locals[main_tid].Some?
            && s.locals[main_tid].v in MainInitSet()
    }

    predicate MainNext(tid: Tid, s: State, s': State, a: Action)
        requires tid in s.locals && s.locals[tid].Some? && s.locals[tid].v.MainThread? && s.locals.Keys <= s'.locals.Keys
    {
        match s.locals[tid].v.mainpc
            case MainPC0 =>
                && a.InputAction?
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && Input(tid, s, s', s'.locals[tid].v.mainstate.x)
                && s'.locals[tid].v.mainpc == MainPC1
            case MainPC1 => 
                && a.OutputAction?
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && Output(tid, s, s', s.locals[tid].v.mainstate.x)
                && s'.locals[tid].v.mainpc == MainPC0
    }

    predicate ThreadNext(tid: Tid, s: State, s': State, a: Action)
    {
        && tid in s.locals
        && s.locals[tid].Some?
        && s.locals.Keys <= s'.locals.Keys
        && (forall tid' :: tid' != tid && tid' in s.locals ==> s'.locals[tid'] == s.locals[tid'])
        && match s.locals[tid].v
            case MainThread(_,_) => MainNext(tid, s, s', a)
    }

    predicate Next(s: State, s': State, a: Action)
    {
        exists tid :: ThreadNext(tid, s, s', a)
    }

    function GetSpec(c: Config): AnnotatedBehaviorSpec<Config, State, Action>
    {
        AnnotatedBehaviorSpec(c, iset s | Init(s),
            iset s, s', a | Next(s, s', a) :: ActionTuple(s, s', a))
    }
}

module AnnotatedHighSpec {
    import opened util_option_s
    import opened Prelude
    import opened AnnotatedBehaviorModule
    import opened ProducerConsumerConfig

    datatype State = State(log: seq<Event>, pending: Option<int>)

    predicate Init(s: State) 
    {
        && s.log == []
        && s.pending.None?
    }

    datatype Action = InputAction(x: int) | OutputAction(x: int)

    predicate Input(s: State, s': State, a: Action)
    {
        && a.InputAction?
        && s.pending.None?
        && s'.pending == Some(a.x)
        && s'.log == s.log + [InputEvent(a.x)]
    }

    predicate Output(s: State, s': State, a: Action)
    {
        && a.OutputAction?
        && a.x == s.pending.v
        && s.pending.Some?
        && s'.pending.None?
        && s'.log == s.log + [OutputEvent(s.pending.v)]
    }

    predicate Next(s: State, s': State, a: Action)
    {
        || Input(s, s', a)
        || Output(s, s', a)
    }

    function GetSpec(c: Config): AnnotatedBehaviorSpec<Config, State, Action>
    {
        AnnotatedBehaviorSpec(c, iset s | Init(s), iset s, s', a | Next(s, s', a) :: ActionTuple(s, s', a))
    }
}

module HighSpec {
    import opened util_option_s
    import opened Prelude
    import opened GeneralRefinementModule

    datatype State = State(log: seq<Event>, pending: Option<int>)

    predicate Init(s: State) 
    {
        && s.log == []
        && s.pending.None?
    }

    predicate Input(s: State, s': State)
    {
        exists x :: 
            && s.pending.None?
            && s'.pending == Some(x)
            && s'.log == s.log + [InputEvent(x)]
    }

    predicate Output(s: State, s': State)
    {
        && s.pending.Some?
        && s'.pending.None?
        && s'.log == s.log + [OutputEvent(s.pending.v)]
    }

    predicate Next(s: State, s': State)
    {
        || Input(s, s')
        || Output(s, s')
    }

    function GetSpec(): Spec<State>
    {
        Spec(iset s | Init(s), iset s, s' | Next(s, s') :: StatePair(s, s'))
    }
}

module PCHighRefinementRelation {
    import opened GeneralRefinementModule
    import ProducerConsumerSpec
    import HighSpec

    predicate IsPrefix<A>(small: seq<A>, big: seq<A>)
    {
        && |small| <= |big|
        && forall i :: 0 <= i < |small| ==> small[i] == big[i]
    }

    function GetRelation(): RefinementRelation<ProducerConsumerSpec.State, HighSpec.State>
    {
        iset l: ProducerConsumerSpec.State, h: HighSpec.State | IsPrefix(l.external, h.log) :: RefinementPair(l, h)
    }
}

module PCSpecRefinesAnnotatedHighSpec {
    import opened util_option_s
    import opened Prelude
    import opened GeneralRefinementModule
    import opened SimulationModule
    import opened ProducerConsumerConfig
    import ProducerConsumerSpec
    import AnnotatedHighSpec
    import PCHighRefinementRelation

    predicate SimulationRelation(l: ProducerConsumerSpec.State, h: AnnotatedHighSpec.State)
    {
        true
    }

    function GetSimulationRelation():
        RefinementRelation<ProducerConsumerSpec.State, AnnotatedHighSpec.State>
    {
        iset l, h| SimulationRelation(l, h) :: RefinementPair(l, h)
    }

    lemma lemma_PCSpecRefinesHighSpec(c: Config)
        ensures SpecRefinesSpec(ProducerConsumerSpec.GetSpec(), AnnotatedHighSpec.GetSpec(c),
                                PCHighRefinementRelation.GetRelation())
    {
        var l_spec := ProducerConsumerSpec.GetSpec();
        var h_spec := AnnotatedHighSpec.GetSpec(c);
        var relation := PCHighRefinementRelation.GetRelation();

        forall lb | BehaviorSatisfiesSpec(lb, l_spec)
            ensures BehaviorRefinesSpec(lb, h_spec, relation)
        {
//            var sr := SimulationRequest(l_spec, h_spec, relation, GetSimulationRelation(), iset s | true);
            var hb := [];
            assert BehaviorRefinesBehavior(lb, hb, relation);
        }
    }
}
