// RUN: /compile:0 /nologo /noNLarith /noCheating:1 /rlimit:1000000


include "../armada/code/dafny/fl/spec/refinement.s.dfy"
include "../armada/code/dafny/util/option.s.dfy"

/*
var x := 0;
x := x + 1;
x := x + 1;
output x;
------------------------
var x := 0;
x := x + 2;
output x;
 */

module Prelude {
    type Tid = int

    datatype Event = Event(value: int)
}

module Layer0 {
    import opened util_option_s
    import opened GeneralRefinementModule
    import opened Prelude
    
    datatype State = State(x: int, log: seq<Event>)

    datatype MainPC = MainPC0 | MainPC1 | MainPC2

    datatype TotalState = TotalState(shared: State, local: Option<MainPC>)

    predicate SharedInit(s: State)
    {
        && s.x == 0
        && s.log == []
    }

    predicate Init(s: TotalState)
    {
        && SharedInit(s.shared)
        && s.local == Some(MainPC0)
    }

    predicate Inv(s: TotalState)
    {
        &&
    }

    predicate Inc(s: State, s': State)
    {
        && s'.x == s.x + 1
        && s'.log == s.log
    }

    predicate Print(s: State, s': State, v: int)
    {
        && s'.x == s.x
        && s'.log == s.log + [Event(v)]
    }


    predicate Next(s: TotalState, s': TotalState)
    {
        match s.local
            case Some(pc) => 
                match pc {
                    case MainPC0 => 
                        && Inc(s.shared, s'.shared)
                        && s'.local == Some(MainPC1)
                    case MainPC1 => 
                        && Inc(s.shared, s'.shared)
                        && s'.local == Some(MainPC2)
                    case MainPC2 => 
                        && Print(s.shared, s'.shared, s.shared.x)
                        && s'.local.None?
                }
            case None => false
    }

    function GetSpec(): Spec<TotalState>
    {
        Spec(iset s | Init(s), iset s, s' | Next(s, s') :: StatePair(s, s'))
    }
}

module Layer1 {
    import opened util_option_s
    import opened GeneralRefinementModule
    import opened Prelude

    datatype State = State(x: int, log: seq<Event>)

    datatype MainPC = MainPC0 | MainPC1

    datatype TotalState = TotalState(shared: State, local: Option<MainPC>)

    predicate SharedInit(s: State)
    {
        && s.x == 0
        && s.log == []
    }

    predicate Init(s: TotalState) 
    {
        && SharedInit(s.shared)
        && s.local == Some(MainPC0)
    }

    predicate IncBy2(s: State, s': State)
    {
        && s'.x == s.x + 2
        && s'.log == s.log
    }

    predicate Print(s: State, s': State, v: int)
    {
        && s'.x == s.x
        && s'.log == s.log + [Event(v)]
    }

    predicate Next(s: TotalState, s': TotalState)
    {
        || s' == s
        || match s.local
            case Some(pc) => 
                match pc {
                    case MainPC0 => 
                        && IncBy2(s.shared, s'.shared)
                        && s'.local == Some(MainPC1)
                    case MainPC1 => 
                        && Print(s.shared, s'.shared, s.shared.x)
                        && s'.local.None?
                }
            case None => false
    }

    function GetSpec(): Spec<TotalState>
    {
        Spec(iset s | Init(s), iset s, s' | Next(s, s') :: StatePair(s, s'))
    }
}

module Sim01 {
    import opened util_option_s
    import opened GeneralRefinementModule
    import Low = Layer0
    import High = Layer1

    predicate RefinementPredicate(l: Low.TotalState, h: High.TotalState) 
    {
        l.shared.log == h.shared.log
    }

    function RefinementSet(): iset<RefinementPair<Low.TotalState, High.TotalState>>
    {
        iset l, h | RefinementPredicate(l, h) :: RefinementPair(l, h)
    }

    lemma lemma_Refinement()
        ensures SpecRefinesSpec(Low.GetSpec(), High.GetSpec(), RefinementSet())
    {
        var l_spec := Low.GetSpec();
        var h_spec := High.GetSpec();
        var relation := RefinementSet();
        forall lb | BehaviorSatisfiesSpec(lb, l_spec)
            ensures BehaviorRefinesSpec(lb, h_spec, relation)
        {
            assert lb[0] in l_spec.init;
            var h0 := High.TotalState(High.State(0, []), Some(High.MainPC0));
            assert RefinementPair(lb[0], h0) in relation;
            assert h0 in h_spec.init;

            var hb := [h0];
            var lh_map: RefinementMap := [RefinementRange(0, 0)];
            var li := 1;

            while li < |lb|
                invariant 0 <= li <= |lb|
                invariant BehaviorSatisfiesSpec(hb, h_spec)
                invariant BehaviorRefinesBehaviorUsingRefinementMap(lb[..li], hb, relation, lh_map)
                invariant IsValidRefinementMap(li, |hb|, lh_map)
            {
                var l := lb[li];
                match l.local 
                    case Some(pc) => {
                        match pc
                            case MainPC0 => {
                            }
                            case MainPC1 => {
                            }
                            case MainPC2 => {
                            }
                    }
                    case None => {
                    }
            }
            assert lb == lb[..li];
        }
    }
}
