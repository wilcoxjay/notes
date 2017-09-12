type Tid(==)

datatype PC = FetchTicket | CheckServing | CritSec 

class State {
    var ticket: int
    var serving: int

    var my_pc: map<Tid, PC>

    // my_ticket[tid] is only meaningful when my_pc[tid] is not FetchTicket
    var my_ticket: map<Tid, int>

    constructor(tids: set<Tid>) 
        ensures Valid() && my_pc.Keys == tids
    {
        new;
        ticket := 0;
        serving := 0;
        my_pc := map tid | tid in tids :: PC.FetchTicket;

        // The initial value of my_ticket is irrelevant, as long as it has the right domain.
        my_ticket := *; assume my_ticket.Keys == tids;
    }

    predicate Valid()
        reads this
    {
        && my_ticket.Keys == my_pc.Keys

        // Mutual exclusion: Two different threads are never in the critical section at once.
        && (forall tid, tid' :: 
            && tid in my_pc 
            && tid' in my_pc 
            && my_pc[tid] == my_pc[tid'] == PC.CritSec 
            ==> tid == tid')

        && serving <= ticket

        // If a thread is in the critical section, then its ticket is the smallest held ticket.
        // (A thread whose PC is FetchTicket does not hold a ticket.)
        && (forall tid, tid' :: 
            && tid != tid'
            && tid in my_pc 
            && tid' in my_pc 
            && my_pc[tid].CritSec? 
            && !my_pc[tid'].FetchTicket? 
            ==> my_ticket[tid] < my_ticket[tid'])

        // Each thread holding a ticket has a ticket number in the interval [serving, ticket).
        && (forall tid :: 
            && tid in my_pc 
            && !my_pc[tid].FetchTicket? 
            ==> serving <= my_ticket[tid] < ticket)

        // No two threads hold the same ticket number.
        && (forall tid, tid' :: 
            && tid in my_pc 
            && tid' in my_pc 
            && !my_pc[tid].FetchTicket? 
            && !my_pc[tid'].FetchTicket? 
            && my_ticket[tid] == my_ticket[tid'] 
            ==> tid == tid') 
    }

    method FetchTicket(tid: Tid)
        modifies this
        requires Valid() && tid in my_pc && my_pc[tid] == PC.FetchTicket
        ensures Valid() && my_pc.Keys == old(my_pc).Keys
    {
        my_ticket := my_ticket[tid := ticket];
        ticket := ticket + 1;
        my_pc := my_pc[tid := PC.CheckServing];
    }

    method CheckServing(tid: Tid)
        modifies this
        requires Valid() && tid in my_pc && my_pc[tid] == PC.CheckServing
        ensures Valid() && my_pc.Keys == old(my_pc).Keys
    {
        if serving == my_ticket[tid] {
            my_pc := my_pc[tid := CritSec];
        } 
    }

    method Exit(tid: Tid)
        modifies this
        requires Valid() && tid in my_pc && my_pc[tid] == PC.CritSec
        ensures Valid() && my_pc.Keys == old(my_pc).Keys
    {
        serving := serving + 1;
        my_pc := my_pc[tid := PC.FetchTicket];
    }
}

method Main()
    decreases *
{
    var tids: set<Tid>;
    var s := new State(tids);

    while tids != {}
        decreases *
        invariant s.Valid() && s.my_pc.Keys == tids
    {
        var tid :| tid in tids;
        match s.my_pc[tid]
            case FetchTicket => s.FetchTicket(tid);
            case CheckServing => s.CheckServing(tid);
            case CritSec => s.Exit(tid);
    }
}
