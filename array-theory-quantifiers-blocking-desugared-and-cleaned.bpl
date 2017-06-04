// RUN: -noinfer -typeEncoding:m -useArrayTheory

const N: int;
axiom N > 0;

type Tid = int;
const unique nil: Tid;

type Ref;

var VC.V: [Ref][int]int;
var VC.Lock: [Ref]Tid;

function {:inline false} g(i: [int] int) : bool;
axiom (forall i: [int] int :: {:inline false} { g(i): bool } g(i): bool <==> true);

implementation NonBlockingChecker_Copy(this_tid: Tid, this_v1: Ref, this_v2: Ref)
{
  L:
    return;
}

procedure NonBlockingChecker_Copy(this_tid: Tid, this_v1: Ref, this_v2: Ref);
  requires true;
  requires this_tid != nil;
  requires VC.Lock[this_v1] == this_tid;
  requires VC.Lock[this_v2] == this_tid;
  modifies VC.V, VC.Lock;
  ensures g(VC.V[this_v2]);
  ensures (exists #tmp_0: [int]int :: {g(#tmp_0)}
  (forall i: int ::
      0 <= i && i < N
         ==> old(VC.V)[this_v1 := #tmp_0][this_v1][i]
           == old(VC.V)[this_v1 := #tmp_0][this_v2][i])
     && true
     && true
     && true);


