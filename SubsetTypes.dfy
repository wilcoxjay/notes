datatype PolarPointRep = PolarPointRep(r: real, theta: real)

type PolarPoint = p: PolarPointRep | 0.0 <= p.r && 0.0 <= p.theta < 360.0
    witness PolarPointRep(0.0, 0.0)
    
predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

type SortedSeq = s: seq<int> | Sorted(s)
