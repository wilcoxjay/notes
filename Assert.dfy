include "Simulation.dfy"

/*
var lock: Option<Tid>

method Worker()
{
    Acquire();
    Release();
}

method Main() 
{
    var t1 := fork Worker;
    var t2 := fork Worker;
    join t1;
    join t2;
}

 */

module Assert {
    import Spec
    import Invariants
    import opened OptionModule

    type Tid = int

    datatype State = State(lock: Option<Tid>, ok: bool)

    datatype MainPC = MainPC0 | MainPC1 | MainPC2 | MainPC3 | MainPC4
       
    datatype MainLocal = MainLocal(t1: Tid, t2: Tid)

    datatype WorkerPC = WorkerPC0 | WorkerPC1 | WorkerPC2

    datatype LocalState = LocalStateMain(mpc: MainPC, mlocal: MainLocal)
                        | LocalStateWorker(wpc: WorkerPC)

    datatype TotalState = TotalState(shared: State, locals: map<Tid, Option<LocalState>>)

    predicate Init(s: TotalState)
    {
        && s.shared.lock.None?
        && s.shared.ok
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
        && s'.locals[tid'] == Some(LocalStateWorker(WorkerPC0))
        && s'.shared == s.shared
    }

    predicate Join(tid: Tid, s: TotalState, s': TotalState, tid': Tid) 
    {
        if tid' in s.locals then
            && s'.locals.Keys == s.locals.Keys
            && s.locals[tid'].None?
            && s'.shared == s.shared
        else 
            && s'.shared.lock == s.shared.lock
            && !s'.shared.ok
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
                && s'.locals[tid].val.mlocal.t2 == s.locals[tid].val.mlocal.t2
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
                && s'.locals[tid].val.mlocal.t2 == s.locals[tid].val.mlocal.t2
                && s'.locals[tid].val.mpc == MainPC3
            case MainPC3 =>
                && s'.locals[tid].Some?
                && s'.locals[tid].val.LocalStateMain?
                && Join(tid, s, s', s.locals[tid].val.mlocal.t2)
                && s'.locals[tid].val.mlocal.t1 == s.locals[tid].val.mlocal.t1
                && s'.locals[tid].val.mpc == MainPC4
            case MainPC4 => 
                && s'.locals == s.locals[tid := None]
                && s'.shared == s.shared
    }

    predicate Acquire(tid: Tid, s: TotalState, s': TotalState)
    {
        && s'.locals.Keys == s.locals.Keys
        && s.shared.lock.None?
        && s'.shared.lock == Some(tid)
        && s'.shared.ok == s.shared.ok

    }

    predicate Release(tid: Tid, s: TotalState, s': TotalState)
    {
        && s'.locals.Keys == s.locals.Keys
        && if s.shared.lock == Some(tid) then 
            && s'.shared.lock.None?
            && s'.shared.ok == s.shared.ok
          else 
            && s'.shared.lock == s.shared.lock
            && !s'.shared.ok
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
                && Release(tid, s, s')
                && s'.locals[tid].val.wpc == WorkerPC2
            case WorkerPC2 => 
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
           case LocalStateWorker(_) => WorkerNext(tid, s, s')
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
                   ==> s.locals[tid].val.mlocal.t1 in s.locals)
                && 
                  (&& s.locals[tid].val.LocalStateMain? 
                   && s.locals[tid].val.mpc in {MainPC2, MainPC3} 
                   ==> s.locals[tid].val.mlocal.t2 in s.locals)
                && 
                  (&& s.locals[tid].val.LocalStateWorker? 
                   && s.locals[tid].val.wpc in {WorkerPC1} 
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
        forall s, s' | 
            && s in inv
            && (s, s') in spec.next
            ensures s' in inv
        {
            var tid :| ThreadNext(tid, s, s');
            match s.locals[tid].val
                case LocalStateMain(_, _) => assert s' in inv;
                case LocalStateWorker(_) => {
                    match s.locals[tid].val.wpc
                        case WorkerPC0 => assert s' in inv;
                        case WorkerPC1 => assert s'.shared.ok; assert s' in inv;
                        case WorkerPC2 => assert s' in inv;
                    }
        }

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
