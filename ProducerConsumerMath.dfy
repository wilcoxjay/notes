include "CivlizedMathPrelude.dfy"
include "../../fl/spec/refinement.s.dfy"
include "../../fl/util/simulation.i.dfy"
include "../../fl/util/refinement/AnnotatedBehavior.i.dfy"
include "../../fl/util/refinement/RefinementConvolution.i.dfy"
include "../../util/collections/seqs.i.dfy"

module ProducerConsumerConfig {
    datatype Config = Config
}

module ProducerConsumer {
    import opened util_option_s
    import opened Prelude
    import opened AnnotatedBehaviorModule
    import opened ProducerConsumerConfig

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

    datatype Action = ForkAction(forked_tid: Tid) | NopAction | InputAction | ProduceAction | ConsumeAction | OutputAction


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

    predicate ProducerNext(tid: Tid, s: State, s': State, a: Action)
        requires tid in s.locals && s.locals[tid].Some? && s.locals[tid].v.ProducerThread? && s.locals.Keys <= s'.locals.Keys
    {
        match s.locals[tid].v.producerpc
            case ProducerPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ProducerThread?
                && a.InputAction?
                && Input(tid, s, s', s'.locals[tid].v.producerstate.x)
                && s'.locals[tid].v.producerpc == ProducerPC1
            case ProducerPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ProducerThread?
                && a.ProduceAction?
                && Produce(tid, s, s', s.locals[tid].v.producerstate.x)
                && s'.locals[tid].v.producerpc == ProducerPC0
    }

    predicate ConsumerNext(tid: Tid, s: State, s': State, a: Action)
        requires tid in s.locals && s.locals[tid].Some? && s.locals[tid].v.ConsumerThread? && s.locals.Keys <= s'.locals.Keys
    {
        match s.locals[tid].v.consumerpc
            case ConsumerPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ConsumerThread?
                && a.ConsumeAction?
                && Consume(tid, s, s', s'.locals[tid].v.consumerstate.x)
                && s'.locals[tid].v.consumerpc == ConsumerPC1
            case ConsumerPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.ConsumerThread?
                && a.OutputAction?
                && Output(tid, s, s', s.locals[tid].v.consumerstate.x)
                && s'.locals[tid].v.consumerpc == ConsumerPC0
    }

    predicate MainNext(tid: Tid, s: State, s': State, a: Action)
        requires tid in s.locals && s.locals[tid].Some? && s.locals[tid].v.MainThread? && s.locals.Keys <= s'.locals.Keys
    {
        match s.locals[tid].v.mainpc
            case MainPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && a.ForkAction?
                && Fork(tid, s, s', ProducerInitSet(), a.forked_tid)
                && s'.locals[tid].v.mainpc == MainPC1
            case MainPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && a.ForkAction?
                && Fork(tid, s, s', ProducerInitSet(), a.forked_tid)
                && s'.locals[tid].v.mainpc == MainPC2
            case MainPC2 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].v.MainThread?
                && a.NopAction?
                && Nop(tid, s, s')
                && s'.locals[tid].v.mainpc == MainPC2
    }

    predicate ThreadNext(tid: Tid, s: State, s': State, a: Action)
    {
        && tid in s.locals
        && s.locals[tid].Some?
        && s.locals.Keys <= s'.locals.Keys
        && (forall tid' :: tid' != tid && tid' in s.locals ==> s'.locals[tid'] == s.locals[tid'])
        && match s.locals[tid].v
            case MainThread(_,_) => MainNext(tid, s, s', a)
            case ProducerThread(_, _) => ProducerNext(tid, s, s', a)
            case ConsumerThread(_, _) => ConsumerNext(tid, s, s', a)
    }

    predicate Next(s: State, s': State, a: Action)
    {
        exists tid :: ThreadNext(tid, s, s', a)
    }

    function GetSpec(c: Config): AnnotatedBehaviorSpec<Config, State, Action>
    {
        AnnotatedBehaviorSpec(c, iset s | Init(s), iset s, s', a | Next(s, s', a) :: ActionTuple(s, s', a))
    }
}

module ProducerConsumerSpec {
    import opened Prelude
    import opened GeneralRefinementModule
    import opened ProducerConsumerConfig
    import opened AnnotatedBehaviorModule

    datatype SharedState = SharedState

    datatype MainPC = MainPC0 | MainPC1 
    datatype MainState = MainState(x: int)

    datatype ThreadState = MainThread(mainpc: MainPC, mainstate: MainState)

    type State = TotalState<SharedState, ThreadState>

    datatype Action = InputAction | OutputAction

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

    function GetNext(): iset<ActionTuple<State, Action>>
    {
        iset s, s', a | Next(s, s', a) :: ActionTuple(s, s', a)
    }

    function GetSpec(c: Config): AnnotatedBehaviorSpec<Config, State, Action>
    {
        AnnotatedBehaviorSpec(c, iset s | Init(s), GetNext())
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

module PrefixModule {
    predicate IsPrefix<A>(small: seq<A>, big: seq<A>)
    {
        && |small| <= |big|
        && forall i :: 0 <= i < |small| ==> small[i] == big[i]
    }
}

module PCSpecHighRefinementRelation {
    import opened GeneralRefinementModule
    import opened PrefixModule
    import ProducerConsumerSpec
    import HighSpec

    function GetRelation(): RefinementRelation<ProducerConsumerSpec.State, HighSpec.State>
    {
        iset l: ProducerConsumerSpec.State, h: HighSpec.State | IsPrefix(l.external, h.log) :: RefinementPair(l, h)
    }
}

module PCPCSpecRefinementRelation {
    import opened GeneralRefinementModule
    import opened PrefixModule
    import ProducerConsumer
    import ProducerConsumerSpec

    function GetRelation(): RefinementRelation<ProducerConsumer.State, ProducerConsumerSpec.State>
    {
        iset l: ProducerConsumer.State, h: ProducerConsumerSpec.State | IsPrefix(l.external, h.external) :: RefinementPair(l, h)
    }
}

module PCHighRefinementRelation {
    import opened GeneralRefinementModule
    import opened PrefixModule
    import ProducerConsumer
    import HighSpec

    function GetRelation(): RefinementRelation<ProducerConsumer.State, HighSpec.State>
    {
        iset l: ProducerConsumer.State, h: HighSpec.State | IsPrefix(l.external, h.log) :: RefinementPair(l, h)
    }
}


module PCRefinesPCSpec {
    import opened util_option_s
    import opened Prelude
    import opened GeneralRefinementModule
    import opened AnnotatedBehaviorModule
    import opened ProducerConsumerConfig
    import opened RefinementConvolutionModule
    import ProducerConsumer
    import ProducerConsumerSpec
    import PCHighRefinementRelation
    import PCSpecHighRefinementRelation

    predicate SimulationRelation(l: ProducerConsumer.State, h: ProducerConsumerSpec.State)
    {
        true
    }

    lemma lemma_PCBehaviorToPCSpecBehavior(
        lb: AnnotatedBehavior<Config, ProducerConsumer.State, ProducerConsumer.Action>
        ) returns (
        hb: AnnotatedBehavior<Config, ProducerConsumerSpec.State, ProducerConsumerSpec.Action>
        )
        requires AnnotatedBehaviorSatisfiesSpec(lb, ProducerConsumer.GetSpec(lb.config))
        ensures lb.config == hb.config
        ensures AnnotatedBehaviorSatisfiesSpec(hb, ProducerConsumerSpec.GetSpec(hb.config))
        ensures BehaviorRefinesWhatOtherBehaviorRefines(lb.states, hb.states, 
            PCHighRefinementRelation.GetRelation(), 
            PCSpecHighRefinementRelation.GetRelation())
    {
        assume false;
    }
}

module PCSpecRefinesHighSpec {
    import opened util_option_s
    import opened Prelude
    import opened GeneralRefinementModule
    import opened AnnotatedBehaviorModule
    import opened ProducerConsumerConfig
    import opened util_collections_seqs_i
    import ProducerConsumerSpec
    import HighSpec
    import PCSpecHighRefinementRelation

    predicate SimulationRelation(l: ProducerConsumerSpec.State, h: HighSpec.State)
    {
        && l.external == h.log
        && exists main_tid :: 
            && l.locals.Keys == {main_tid}
            && l.locals[main_tid].Some?
            && match l.locals[main_tid].v.mainpc
                case MainPC0 => h.pending.None?
                case MainPC1 => h.pending == Some(l.locals[main_tid].v.mainstate.x)
    }


    lemma lemma_PCSpecBehaviorToHighBehavior(
        lb: AnnotatedBehavior<Config, ProducerConsumerSpec.State, ProducerConsumerSpec.Action>
        ) returns (
        hb: seq<HighSpec.State>
        )
        requires AnnotatedBehaviorSatisfiesSpec(lb, ProducerConsumerSpec.GetSpec(lb.config))
        ensures BehaviorSatisfiesSpec(hb, HighSpec.GetSpec())
        ensures BehaviorRefinesBehavior(lb.states, hb, PCSpecHighRefinementRelation.GetRelation())
    {
        assert ProducerConsumerSpec.Init(lb.states[0]);
        var hb0 := HighSpec.State([], None);
        assert SimulationRelation(lb.states[0], hb0);
        hb := [hb0];

        while |hb| < |lb.states|
            invariant 0 <= |hb| <= |lb.states|
            invariant forall i :: 0 <= i < |hb| ==> SimulationRelation(lb.states[i], hb[i])
            invariant BehaviorSatisfiesSpec(hb, HighSpec.GetSpec())
        {
            var i := |hb|-1;
            var l, l', a := lb.states[i], lb.states[i+1], lb.trace[i];
            var h := hb[i];
            assert SimulationRelation(l, h);
            assert ActionTuple(l, l', a) in ProducerConsumerSpec.GetNext();
            var tid :| ProducerConsumerSpec.ThreadNext(tid, l, l', a);
            assert l.locals.Keys == {tid};
            var h': HighSpec.State;
            match l.locals[tid].v.mainpc {
                case MainPC0 => {
                    var x := l'.locals[tid].v.mainstate.x;
                    h' := HighSpec.State(h.log + [InputEvent(x)], Some(x));
                }
                case MainPC1 => {
                    var x := l.locals[tid].v.mainstate.x;
                    h' := HighSpec.State(h.log + [OutputEvent(x)], None);
                }
            }

            hb := hb + [h'];
        }

        var lh_map := ConvertMapToSeq(|hb|, map i | 0 <= i < |hb| :: RefinementRange(i, i));
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb, PCSpecHighRefinementRelation.GetRelation(), lh_map);
    }
}
