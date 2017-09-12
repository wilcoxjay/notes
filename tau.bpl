/*

data: [Tid] bool;
barrier: [Tid] bool;

worker(tid) {

  // Note: TSO semantics.
  data[tid] := true;
  barrier[tid] := true;

  assert forall x :: barrier[x] ==> data[x];
}

*/

type Tid;

var {:layer 0,2} data: [Tid] bool;
var {:layer 0,2} barrier: [Tid] bool;

var {:layer 0,1} queue_start: [Tid] int;
var {:layer 0,1} queue_end: [Tid] int;

procedure {:yields} {:layer 0,1} TSO_WriteData({:linear "tid"} tid: Tid);
ensures {:atomic} |{A: queue_end[tid] := 1; return true; }|;

procedure {:yields} {:layer 0,1} TSO_WriteBarrier({:linear "tid"} tid: Tid);
ensures {:atomic} |{A: queue_end[tid] := 2; return true; }|;

procedure {:yields} {:layer 0,1} TSO_Tau({:linear "tid"}tid: Tid);
ensures {:atomic} |{A:
  goto B, C, D;
B:
  assume queue_start[tid] < queue_end[tid] && queue_start[tid] == 0;
  queue_start[tid] := 1;
  data[tid] := true;
  return true;
C:
  assume queue_start[tid] < queue_end[tid] && queue_start[tid] == 1;
  queue_start[tid] := 2;
  barrier[tid] := true;
  return true;
D:
  return true;
}|;

procedure {:yields} {:layer 0,1} TSO_Fence({:linear "tid"} tid: Tid);
ensures {:atomic} |{A: assume queue_start[tid] == queue_end[tid]; return true; }|;

procedure {:yields} {:layer 1,2} Worker({:linear "tid"} tid: Tid)
ensures {:atomic} |{A: return true; }|;
{
    yield;
    call TSO_WriteData(tid);
    yield;
    call TSO_Tau(tid);
    yield;
    call TSO_Tau(tid);
    yield;
    call TSO_WriteBarrier(tid);
    yield;
    call TSO_Tau(tid);
    yield;
    call TSO_Tau(tid);
    yield;
    assert {:layer 1} (forall x: Tid :: barrier[tid] ==> data[tid]);
    call TSO_Fence(tid);
    yield;
}


function {:builtin "MapConst"} TidMapConstBool(bool): [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  TidMapConstBool(false)[x := true]
}

