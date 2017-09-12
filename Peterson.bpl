type Tid = int;

const nil: Tid;
axiom nil == -1;

function {:builtin "MapConst"} TidMapConstBool(bool): [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  TidMapConstBool(false)[x := true]
}


var {:layer 0,2} victim: Tid;
var {:layer 0,2} flag: [Tid] bool;

var {:layer 1,3} lock: Tid;

procedure {:yields} {:layer 0,2} RaiseFlag({:linear "tid"} tid: Tid);
  ensures {:atomic} |{ A: assert tid == 0 || tid == 1; flag[tid] := true; return true; }|;

procedure {:yields} {:layer 0,2} LowerFlag({:linear "tid"} tid: Tid);
  ensures {:atomic} |{ A: assert tid == 0 || tid == 1; flag[tid] := false; return true; }|;

procedure {:yields} {:layer 0,2} SetVictim({:linear "tid"} tid: Tid);
  ensures {:atomic} |{ A: assert tid == 0 || tid == 1; victim := tid; return true; }|;

procedure {:yields} {:layer 0,2} GetFlag({:linear "tid"} tid: Tid) returns (x: bool);
  ensures {:atomic} |{ A: assert tid == 0 || tid == 1; x := flag[1-tid]; return true; }|;

procedure {:yields} {:layer 0,2} GetVictim() returns (v: Tid);
  ensures {:atomic} |{ A: v := victim; return true; }|;

procedure {:yields} {:layer 1,3} SetLock({:linear "tid"} tid: Tid);
  ensures {:atomic} |{ A: assert tid == 0 || tid == 1; lock := tid; return true; }|;


procedure {:yields} {:layer 2,3} Acquire({:linear "tid"} tid: Tid)
  requires {:layer 2} tid == 0 || tid == 1;
  ensures {:atomic} |{ A: assume lock == nil; lock := tid; return true; }|;
{
    var f: bool;
    var v: Tid;

    yield;
    call RaiseFlag(tid);
    yield;
    call SetVictim(tid);
    yield;

    while (true)
    {
        call f := GetFlag(tid);
        if (!f) { break; }
        yield;
        call v := GetVictim();
        if (v != tid) { break; }
        yield;
    }

    yield;
    assert {:layer 2} lock == nil;

    call SetLock(tid);

    yield;
    assert {:layer 2} lock == tid;
}
