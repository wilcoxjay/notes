// RUN: /compile:0 /print:log.bpl /rprint:log.dfy

type Tid = x: int | 0 <= x <= 1

class State {
    var victim: Tid
    var flag: map<Tid, bool>
    var critsec: map<Tid, bool>

    constructor() 
        ensures forall tid': Tid :: tid' in flag 
        ensures forall tid': Tid :: tid' in critsec && !critsec[tid']
    {
        flag := map tid :: false;
        critsec := map tid :: false;
    }
}

iterator PetersonThread(tid: Tid, s: State) yields (critsec: bool)
    requires s != null
    yield requires forall tid': Tid :: tid' in s.flag
    yield ensures forall tid': Tid :: tid' in s.flag
    modifies s
    ensures forall tid': Tid :: tid' in s.flag
    ensures true in critsecs
{
    var other: Tid := 1-tid;

    s.flag := s.flag[tid := true];
    critsec := false;
    yield;
    s.victim := tid;
    yield;
    while true 
        invariant forall tid': Tid :: tid' in s.flag
    {
        if !s.flag[other] { break; }
        yield;
        if s.victim != tid { break; }
        yield;
    }

    // critical section here
    critsec := true;
    yield;

    // exit critical section
    s.flag := s.flag[tid := false];
}

method Main()
    decreases *
{
    var s := new State();

    var t1 := new PetersonThread(0, s);
    var t2 := new PetersonThread(1, s);

    var more1, more2 := true, true;

    while true 
        decreases *
        invariant fresh(t1._new) 
        invariant fresh(t2._new) 

        invariant {s, t1, t2} !! t1._new !! t2._new

        invariant more1 ==> t1.Valid() 
        invariant more2 ==> t2.Valid() 
        invariant forall tid: Tid :: tid in s.flag
    {
        if {
            case more1 => more1 := t1.MoveNext(); 
            case more2 => more2 := t2.MoveNext();
            case true => {}
        }
    }
}
