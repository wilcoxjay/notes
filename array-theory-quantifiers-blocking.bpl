// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory

const N: int;
axiom N > 0;

type Tid = int;
const unique nil: Tid;

type Ref;

var {:layer 0,2} VC.V : [Ref] [int] int;
var {:layer 0,2} VC.Lock : [Ref] Tid;

procedure {:yields} {:layer 1,2} Copy({:linear "tid" } tid: Tid, v1: Ref, v2: Ref);
  requires {:layer 1} tid != nil;
  requires {:layer 1} VC.Lock[v1] == tid;
  requires {:layer 1} VC.Lock[v2] == tid;
  ensures {:both} |{
          var Vnew: [int] int;
        A:
          assert tid != nil;
          assert VC.Lock[v1] == tid;
          assert VC.Lock[v2] == tid;
          VC.V[v1] := Vnew;
          assume (forall i: int :: 0 <= i && i < N ==> VC.V[v1][i] == VC.V[v2][i]);
          return true;
       }|;

function {:builtin "MapConst"} TidMapConstBool(bool): [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  TidMapConstBool(false)[x := true]
}
