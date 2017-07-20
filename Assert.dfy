include "Simulation.dfy"

/*
var lock: Option<Tid>
var x: int := 0

method Worker()
{
    Acquire();
    var t := x;
    x := t + 1;
    Release();
}

method Main() 
{
    var t1 := fork Worker;
    var t2 := fork Worker;
    join t1;
    join t2;
    print x;
}

 */

module Assert {
    import Spec
    import Invariants
    import opened OptionModule

    type Tid = int

    datatype Event = Event(output: int)

    datatype State = State(lock: Option<Tid>, x: int, log: seq<Event>, ok: bool)

    datatype MainPC = MainPC0 | MainPC1 | MainPC2 | MainPC3 | MainPC4 | MainPC5
       
    datatype MainLocal = MainLocal(t1: Tid, t2: Tid)

    datatype WorkerPC = WorkerPC0 | WorkerPC1 | WorkerPC2 | WorkerPC3 | WorkerPC4

    datatype WorkerLocal = WorkerLocal(t: int)

    datatype LocalState = LocalStateMain(mpc: MainPC, mlocal: MainLocal)
                        | LocalStateWorker(wpc: WorkerPC, wlocal: WorkerLocal)

    datatype TotalState = TotalState(shared: State, locals: map<Tid, Option<LocalState>>)

    predicate Init(s: TotalState)
    {
        && s.shared.lock.None?
        && s.shared.ok
        && s.shared.x == 0
        && s.shared.log == []
        && exists main_tid :: 
            && s.locals.Keys == {main_tid}
            && s.locals[main_tid].Some? 
            && s.locals[main_tid].val.LocalStateMain? 
            && s.locals[main_tid].val.mpc == MainPC0
    }

    predicate Fork(tid: Tid, s: TotalState, s': TotalState, tid': Tid) 
    {
        && tid' !in s.locals
        && s'.locals.Keys == {tid'} + s.locals.Keys
        && s'.locals[tid'].Some?
        && s'.locals[tid'].val.LocalStateWorker? 
        && s'.locals[tid'].val.wpc == WorkerPC0
        && s'.shared == s.shared
    }

    predicate Join(tid: Tid, s: TotalState, s': TotalState, tid': Tid) 
    {
        if tid' in s.locals && tid' != tid then
            && s'.locals.Keys == s.locals.Keys
            && s.locals[tid'].None?
            && s'.shared == s.shared
        else 
            && s'.shared.lock == s.shared.lock
            && s'.shared.x == s.shared.x
            && s'.shared.log == s.shared.log
            && !s'.shared.ok
    }

    predicate Print(tid: Tid, s: TotalState, s': TotalState, value: int)
    {
        && s'.locals.Keys == s.locals.Keys
        && s'.shared.log == s.shared.log + [Event(value)]
        && s'.shared.x == s.shared.x
        && s'.shared.lock == s.shared.lock
        && s'.shared.ok == s.shared.ok
    }

    predicate MainNext(tid: Tid, s: TotalState, s': TotalState)
        requires && s.locals.Keys <= s'.locals.Keys
                 && tid in s.locals 
                 && s.locals[tid].Some?
                 && s.locals[tid].val.LocalStateMain?
    {
        match s.locals[tid].val.mpc
            case MainPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Fork(tid, s, s', s'.locals[tid].val.mlocal.t1)
                && s'.locals[tid].val.mpc == MainPC1
            case MainPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Fork(tid, s, s', s'.locals[tid].val.mlocal.t2)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mpc == MainPC2
            case MainPC2 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Join(tid, s, s', s.locals[tid].val.mlocal.t1)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mlocal.t2 == s.locals[tid].val.mlocal.t2
                && s'.locals[tid].val.mpc == MainPC3
            case MainPC3 =>
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Join(tid, s, s', s.locals[tid].val.mlocal.t2)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mlocal.t2 == s.locals[tid].val.mlocal.t2
                && s'.locals[tid].val.mpc == MainPC4
            case MainPC4 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Print(tid, s, s', s.shared.x)
                && s'.locals[tid].val.mpc == MainPC5
            case MainPC5 => 
                && s'.locals == s.locals[tid := None]
                && s'.shared == s.shared
    }

    predicate Acquire(tid: Tid, s: TotalState, s': TotalState)
    {
        && s'.locals.Keys == s.locals.Keys
        && s.shared.lock.None?
        && s'.shared.lock == Some(tid)
        && s'.shared.ok == s.shared.ok
        && s'.shared.x == s.shared.x
    }

    predicate Release(tid: Tid, s: TotalState, s': TotalState)
    {
        && s'.locals.Keys == s.locals.Keys
        && if s.shared.lock == Some(tid) then 
            && s'.shared.lock.None?
            && s'.shared.ok == s.shared.ok
            && s'.shared.log == s.shared.log
            && s'.shared.x == s.shared.x
          else 
            && s'.shared.lock == s.shared.lock
            && !s'.shared.ok
    }

    predicate Read(tid: Tid, s: TotalState, s': TotalState, t: int)
    {
        && s'.locals.Keys == s.locals.Keys
        && s'.shared == s.shared
        && t == s.shared.x
    }

    predicate Write(tid: Tid, s: TotalState, s': TotalState, t: int)
    {
        && s'.locals.Keys == s.locals.Keys
        && s'.shared.lock == s.shared.lock
        && s'.shared.ok == s.shared.ok
        && s'.shared.x == t
        && s'.shared.log == s.shared.log
    }

    predicate WorkerNext(tid: Tid, s: TotalState, s': TotalState)
        requires && s.locals.Keys <= s'.locals.Keys
                 && tid in s.locals 
                 && s.locals[tid].Some?
                 && s.locals[tid].val.LocalStateWorker?
    {
        match s.locals[tid].val.wpc
            case WorkerPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateWorker?
                && Acquire(tid, s, s')
                && s'.locals[tid].val.wpc == WorkerPC1
            case WorkerPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateWorker?
                && Read(tid, s, s', s'.locals[tid].val.wlocal.t)
                && s'.locals[tid].val.wpc == WorkerPC2
            case WorkerPC2 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateWorker?
                && Write(tid, s, s', s'.locals[tid].val.wlocal.t + 1)
                && s'.locals[tid].val.wpc == WorkerPC3
            case WorkerPC3 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateWorker?
                && Release(tid, s, s')
                && s'.locals[tid].val.wpc == WorkerPC4
            case WorkerPC4 => 
                && s'.locals == s.locals[tid := None]
                && s'.shared == s.shared
    }

    predicate ThreadNext(tid: Tid, s: TotalState, s': TotalState)
    {
        && tid in s.locals
        && s.locals.Keys <= s'.locals.Keys
        && (forall tid' :: tid' != tid && tid' in s.locals ==> s'.locals[tid'] == s.locals[tid'])
        && s.locals[tid].Some?
        && match s.locals[tid].val
           case LocalStateMain(_, _) => MainNext(tid, s, s')
           case LocalStateWorker(_, _) => WorkerNext(tid, s, s')
    }

    predicate Next(s: TotalState, s': TotalState)
    {
        exists tid :: ThreadNext(tid, s, s')
    }

    predicate Inv(s: TotalState)
    {
        && s.shared.ok
        && forall tid :: 
            && tid in s.locals 
            && s.locals[tid].Some?
            ==> &&
                  (&& s.locals[tid].val.LocalStateMain? 
                   && s.locals[tid].val.mpc in {MainPC1, MainPC2} 
                   ==> && s.locals[tid].val.mlocal.t1 in s.locals
                       && s.locals[tid].val.mlocal.t1 != tid)
                && 
                  (&& s.locals[tid].val.LocalStateMain? 
                   && s.locals[tid].val.mpc in {MainPC2, MainPC3} 
                   ==> && s.locals[tid].val.mlocal.t2 in s.locals
                       && s.locals[tid].val.mlocal.t2 != tid)
                && 
                  (&& s.locals[tid].val.LocalStateWorker? 
                   && s.locals[tid].val.wpc in {WorkerPC1, WorkerPC2, WorkerPC3}
                   ==> s.shared.lock == Some(tid))
    }

    function InvSet(): iset<TotalState>
    {
        iset s | Inv(s)
    }

    lemma lemma_InvInvariant()
        ensures Invariants.IsInvariant(InvSet(), GetSpec())
    {
        var inv := InvSet();
        var spec := GetSpec();

        Invariants.EstablishInvariantByInduction(InvSet(), GetSpec());
    }

    predicate IsOk(s: TotalState) 
    {
        s.shared.ok
    }

    function OkSet(): iset<TotalState> 
    {
        iset s | IsOk(s)
    }

    function GetSpec(): Spec.T<TotalState>
    {
        Spec.Make(iset s | Init(s), iset s, s' | Next(s, s') :: (s, s'))
    }

    lemma lemma_OkInvariant()
        ensures Invariants.IsInvariant(OkSet(), GetSpec())
    {
        lemma_InvInvariant();
        Invariants.InvariantImplies(InvSet(), OkSet(), GetSpec());
    }
}

module AssertReduced {
    import Spec
    import Invariants
    import opened OptionModule

    type Tid = int

    datatype Event = Event(output: int)

    datatype State = State(x: int, log: seq<Event>, main_tid: Tid)

    datatype MainPC = MainPC0 | MainPC1 | MainPC2 | MainPC3 | MainPC4 | MainPC5
       
    datatype MainLocal = MainLocal(t1: Tid, t2: Tid)

    datatype WorkerPC = WorkerPC0 | WorkerPC1 | WorkerPC2 | WorkerPC3 | WorkerPC4

    datatype WorkerLocal = WorkerLocal(t: int)

    datatype LocalState = LocalStateMain(mpc: MainPC, mlocal: MainLocal)
                        | LocalStateWorker(wpc: WorkerPC, wlocal: WorkerLocal)

    datatype TotalState = TotalState(shared: State, locals: map<Tid, Option<LocalState>>)

    predicate Init(s: TotalState)
    {
        && s.shared.x == 0
        && s.shared.log == []
        && exists main_tid :: 
            && s.shared.main_tid == main_tid
            && s.locals.Keys == {main_tid}
            && s.locals[main_tid].Some? 
            && s.locals[main_tid].val.LocalStateMain? 
            && s.locals[main_tid].val.mpc == MainPC0
    }

    predicate Fork(tid: Tid, s: TotalState, s': TotalState, tid': Tid) 
    {
        && tid' !in s.locals
        && s'.locals.Keys == {tid'} + s.locals.Keys
        && s'.locals[tid'].Some?
        && s'.locals[tid'].val.LocalStateWorker? 
        && s'.locals[tid'].val.wpc == WorkerPC0
        && s'.shared == s.shared
    }

    predicate Join(tid: Tid, s: TotalState, s': TotalState, tid': Tid) 
    {
        && tid' in s.locals 
        && tid' != tid
        && s'.locals.Keys == s.locals.Keys
        && s.locals[tid'].None?
        && s'.shared == s.shared
    }

    predicate Print(tid: Tid, s: TotalState, s': TotalState, value: int)
    {
        && s'.locals.Keys == s.locals.Keys
        && s'.shared.log == s.shared.log + [Event(value)]
        && s'.shared.x == s.shared.x
        && s'.shared.main_tid == s.shared.main_tid
    }

    predicate MainNext(tid: Tid, s: TotalState, s': TotalState)
        requires && s.locals.Keys <= s'.locals.Keys
                 && tid in s.locals 
                 && s.locals[tid].Some?
                 && s.locals[tid].val.LocalStateMain?
    {
        match s.locals[tid].val.mpc
            case MainPC0 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Fork(tid, s, s', s'.locals[tid].val.mlocal.t1)
                && s'.locals[tid].val.mpc == MainPC1
            case MainPC1 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Fork(tid, s, s', s'.locals[tid].val.mlocal.t2)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mpc == MainPC2
                && s.locals[tid].val.mlocal.t1 in s.locals
                && s.locals[tid].val.mlocal.t1 != tid
            case MainPC2 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Join(tid, s, s', s.locals[tid].val.mlocal.t1)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mlocal.t2 == s.locals[tid].val.mlocal.t2
                && s'.locals[tid].val.mpc == MainPC3
                && s.locals[tid].val.mlocal.t1 in s.locals
                && s.locals[tid].val.mlocal.t1 != tid
                && s.locals[tid].val.mlocal.t2 in s.locals
                && s.locals[tid].val.mlocal.t2 != tid
            case MainPC3 =>
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Join(tid, s, s', s.locals[tid].val.mlocal.t2)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mlocal.t2 == s.locals[tid].val.mlocal.t2
                && s'.locals[tid].val.mpc == MainPC4
                && s.locals[tid].val.mlocal.t2 in s.locals
                && s.locals[tid].val.mlocal.t2 != tid
            case MainPC4 => 
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Print(tid, s, s', s.shared.x)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mlocal.t2 == s.locals[tid].val.mlocal.t2
                && s'.locals[tid].val.mpc == MainPC5
            case MainPC5 => 
                && s'.locals == s.locals[tid := None]
                && s'.shared == s.shared
    }

    predicate Inc(tid: Tid, s: TotalState, s': TotalState)
    {
        && s'.locals.Keys == s.locals.Keys
        && s'.shared.x == s.shared.x + 1
        && s'.shared.log == s.shared.log
        && s'.shared.main_tid == s.shared.main_tid
    }

    predicate WorkerNext(tid: Tid, s: TotalState, s': TotalState)
        requires && s.locals.Keys <= s'.locals.Keys
                 && tid in s.locals 
                 && s.locals[tid].Some?
                 && s.locals[tid].val.LocalStateWorker?
    {
        match s.locals[tid].val.wpc
            case WorkerPC0 => 
                && Inc(tid, s, s')
                && s'.locals == s.locals[tid := None]
            case WorkerPC1 => false
            case WorkerPC2 => false
            case WorkerPC3 => false
            case WorkerPC4 => false
    }

    predicate ThreadNext(tid: Tid, s: TotalState, s': TotalState)
    {
        && tid in s.locals
        && s.locals.Keys <= s'.locals.Keys
        && (forall tid' :: tid' != tid && tid' in s.locals ==> s'.locals[tid'] == s.locals[tid'])
        && s.locals[tid].Some?
        && match s.locals[tid].val
           case LocalStateMain(_, _) => MainNext(tid, s, s')
           case LocalStateWorker(_, _) => WorkerNext(tid, s, s')
    }

    predicate Next(s: TotalState, s': TotalState)
    {
        exists tid :: ThreadNext(tid, s, s')
    }

    function GetSpec(): Spec.T<TotalState>
    {
        Spec.Make(iset s | Init(s), iset s, s' | Next(s, s') :: (s, s'))
    }

    function Contribution(tid: Tid, s: TotalState): int
        ensures 0 <= Contribution(tid, s) <= 1
    {
        if tid in s.locals && s.locals[tid].Some? then
            0
        else 
            1
    }

    predicate Inv(s: TotalState) 
    {
        var main_tid := s.shared.main_tid;
        && main_tid in s.locals 
        && (s.locals[main_tid].Some? ==> s.locals[main_tid].val.LocalStateMain?)
        && (forall tid :: 
            && tid != main_tid 
            && tid in s.locals 
            && s.locals[tid].Some?
            ==> && s.locals[tid].val.LocalStateWorker?
                && s.locals[s.shared.main_tid].Some?)
        && if s.locals[main_tid].Some? then
            && (s.locals[main_tid].val.mpc != MainPC5 ==> s.shared.log == [])
            && match s.locals[main_tid].val.mpc
                case MainPC0 => 
                    && s.locals.Keys == {main_tid}
                    && s.shared.x == 0
                case MainPC1 => 
                    var t1 := s.locals[main_tid].val.mlocal.t1;
                    && s.locals.Keys == {main_tid, t1}
                    && s.shared.x == Contribution(t1, s)
                case MainPC2 => 
                    var t1 := s.locals[main_tid].val.mlocal.t1;
                    var t2 := s.locals[main_tid].val.mlocal.t2;
                    && s.locals.Keys == {main_tid, t1, t2}
                    && t1 != t2
                    && s.shared.x == Contribution(t1, s) + 
                                     Contribution(t2, s)
                case MainPC3 => 
                    var t1 := s.locals[main_tid].val.mlocal.t1;
                    var t2 := s.locals[main_tid].val.mlocal.t2;
                    && s.locals.Keys == {main_tid, t1, t2}
                    && t1 != t2
                    && s.locals[t1].None? 
                    && s.shared.x == 1 + Contribution(t2, s)
                case MainPC4 => 
                    var t1 := s.locals[main_tid].val.mlocal.t1;
                    var t2 := s.locals[main_tid].val.mlocal.t2;
                    && s.locals.Keys == {main_tid, t1, t2}
                    && t1 != t2
                    && s.locals[t1].None? 
                    && s.locals[t2].None?
                    && s.shared.x == 2
                case MainPC5 =>
                    var t1 := s.locals[main_tid].val.mlocal.t1;
                    var t2 := s.locals[main_tid].val.mlocal.t2;
                    && s.locals.Keys == {main_tid, t1, t2}
                    && t1 != t2
                    && s.locals[t1].None? 
                    && s.locals[t2].None?
                    && |s.shared.log| == 1
                    && s.shared.log[0] == Event(2)
           else 
               s.shared.log == [Event(2)]
    }

    function InvSet(): iset<TotalState>
    {
        iset s | Inv(s)
    }

    lemma lemma_InvInvariant()
        ensures Invariants.IsInvariant(InvSet(), GetSpec())
    {
        var inv := InvSet();
        var spec := GetSpec();

        Invariants.EstablishInvariantByInduction(InvSet(), GetSpec());
    }
}
