// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory

const N: int;

type Tid = int;

type Ref;

var {:layer 0,2} VC.V : [Ref] [int] int;
var {:layer 0,2} VC.Lock : [Ref] Tid;

// Comment this axiom out to see that the commutativity check fails.
axiom (forall m : [Ref][int]int, r1,r2 : Ref, i,x : int ::
  r1 != r2 ==>
  m[r1 := m[r1][i := x]][r2] == m[r2]);

procedure {:yields} {:layer 1,2} VCLeq({:linear "tid"} tid: Tid, v1: Ref, v2: Ref) returns (res: bool);
  requires {:layer 1} VC.Lock[v1] == tid;
  requires {:layer 1} VC.Lock[v2] == tid;
  ensures {:both} |{A:
            assert VC.Lock[v1] == tid;
            assert VC.Lock[v2] == tid;
            res := (forall i : int :: 0 <= i && i < N ==> VC.V[v1][i] <= VC.V[v2][i]);
            return true;
    }|;

procedure {:yields} {:layer 1,2} Inc({:linear "tid"} tid: Tid, v: Ref, i: int);
  requires {:layer 1} VC.Lock[v] == tid;
  ensures {:both} |{A:
          assert VC.Lock[v] == tid;
          VC.V[v][i] := VC.V[v][i] + 1;
          return true;
  }|;

function {:builtin "MapConst"} TidMapConstBool(bool): [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  TidMapConstBool(false)[x := true]
}
