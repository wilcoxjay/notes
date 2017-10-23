// RUN: /compile:0 /rlimit:1000000

module Prelude {
    function Last<T>(s: seq<T>): T
        requires s != []
    {
        s[|s| - 1]
    }

    function ButLast<T>(s: seq<T>): seq<T>
        requires s != []
    {
        s[..|s| - 1]
    }

    function Min(a: int, b: int): int
    {
        if a < b then a else b
    }

    function {:opaque} MapToSeq<T>(n: nat, m: map<int, T>): (s: seq<T>)
        requires forall i | 0 <= i < n :: i in m
        ensures |s| == n && forall i | 0 <= i < n :: s[i] == m[i]
    {
        if n == 0 then
            []
        else
            MapToSeq(n - 1, m) + [m[n - 1]]
    }

    function FoldLeft<A, B>(f: (A, B) -> B, acc: B, s: seq<A>): B
    {
        if s == [] then
            acc
        else
            FoldLeft(f, f(s[0], acc), s[1..])
    }

    function SumReals(s: seq<real>): real
    {
        if s == [] then
            0.0
        else
            s[0] + SumReals(s[1..])
    }

    function Range(lo: int, hi: int): seq<int>
        decreases hi - lo
    {
        if lo >= hi then
            []
        else
            [lo] + Range(lo + 1, hi)
    }

    lemma lemma_RangeRange(lo: int, hi: int)
        decreases hi - lo
        ensures forall x | x in Range(lo, hi) :: lo <= x < hi
    {}

    function FoldLeftPartial<A, B>(f: (A, B) --> B, acc: B, s: seq<A>): B
        requires forall x, y | x in s :: f.requires(x, y)
    {
        if s == [] then
            acc
        else
            FoldLeftPartial(f, f(s[0], acc), s[1..])
    }

    lemma lemma_FoldLeftPartialInductionPrinciple<A, B>(
        f: (A, B) --> B,
        acc: B,
        s: seq<A>,
        p: B -> bool
        )
        requires forall x, y | x in s :: f.requires(x, y)
        requires p(acc)
        requires forall x, y | x in s && p(y) :: p(f(x, y))
        ensures p(FoldLeftPartial(f, acc, s))
    {
        if s != [] {
            lemma_FoldLeftPartialInductionPrinciple(f, f(s[0], acc), s[1..], p);
        }
    }

    function ArgMaxPartial<T>(f: T --> real, s: seq<T>): T
        requires s != [] && forall x | x in s :: f.requires(x)
    {
        var t := s[0];
        if forall x | x in s :: f(x) <= f(t) then t
        else ArgMaxPartial(f, s[1..])
    }

    lemma lemma_ArgMaxPartialSpec<T>(f: T --> real, s: seq<T>)
        requires s != [] && forall x | x in s :: f.requires(x)
        ensures var arg := ArgMaxPartial(f, s);
            && arg in s
            && forall x | x in s :: f(x) <= f(arg)
    {
        var t := s[0];
        if ! forall x | x in s :: f(x) <= f(t) {
            lemma_ArgMaxPartialSpec(f, s[1..]);
        }
    }

    lemma lemma_ArgMaxPartialSpecAuto<T>()
        ensures forall f: T --> real, s: seq<T> {:induction false} |
            s != [] && forall x | x in s :: f.requires(x) ::
            var arg := ArgMaxPartial(f, s);
                && arg in s
                && forall x | x in s :: f(x) <= f(arg)
    {
        forall f: T --> real, s: seq<T> |
            s != [] && forall x | x in s :: f.requires(x)
        {
            lemma_ArgMaxPartialSpec(f, s);
        }
    }

    lemma lemma_ArgMaxPartialIn<T>(f: T --> real, s: seq<T>)
        requires s != [] && forall x | x in s :: f.requires(x)
        ensures ArgMaxPartial(f, s) in s
    {}

    lemma lemma_ArgMaxPartialInAuto<T>()
        ensures forall f: T --> real, s: seq<T> {:induction false} |
            s != [] && forall x | x in s :: f.requires(x) ::
            ArgMaxPartial(f, s) in s
    {
        forall f: T --> real, s: seq<T> |
            s != [] && forall x | x in s :: f.requires(x)
        {
            lemma_ArgMaxPartialIn(f, s);
        }
    }


    function AbsReal(x: real): real
    {
        if x < 0.0 then - x else x
    }

    function Repeat<T>(n: nat, x: T): (ans: seq<T>)
        ensures |ans| == n
        ensures forall i | 0 <= i < n :: ans[i] == x
    {
       if n == 0 then
           []
       else
           [x] + Repeat(n - 1, x)
    }

    function Map<A, B>(f: A --> B, xs: seq<A>): seq<B>
        requires forall x | x in xs :: f.requires(x)
    {
        MapToSeq(|xs|, map i | 0 <= i < |xs| :: f(xs[i]))
    }

    function ZipWith<A, B, C>(f: (A,B) -> C, xs: seq<A>, ys: seq<B>): (zs: seq<C>)
        requires |xs| == |ys|
        ensures |zs| == |xs|
    {
        MapToSeq(|xs|, map i | 0 <= i < |xs| :: f(xs[i], ys[i]))
    }
}

module Vector {
    import opened Prelude

    export provides T, FromSeq, ToSeq, Add, Scale, Dim,
                    Get, lemma_GetFromSeq, lemma_GetToSeq, lemma_GetAdd, lemma_GetScale,
                    lemma_GetAuto,
                    LinearCombine, Origin,
                    Span, LinearlyIndependent
           reveals SeqSameDim, SeqDim, IsetDim, IsetSameDim


    type T(==) = seq<real>

    function Dim(v: T): nat
    {
        |v|
    }

    function Get(v: T, i: int): real
        requires 0 <= i < Dim(v)
    {
        v[i]
    }

    function FromSeq(v: seq<real>): T
        ensures Dim(FromSeq(v)) == |v|
    {
        v
    }

    lemma lemma_GetFromSeq()
        ensures forall v, i | 0 <= i < |v| :: Get(FromSeq(v), i) == v[i]
    {}


    function ToSeq(v: T): seq<real>
        ensures Dim(v) == |ToSeq(v)|
    {
        v
    }

    lemma lemma_GetToSeq()
        ensures forall v, i | 0 <= i < Dim(v) :: Get(v, i) == ToSeq(v)[i]
    {}

    function Add(u: T, v: T): (ans: T)
        requires Dim(u) == Dim(v)
        ensures Dim(ans) == Dim(u)
    {
        MapToSeq(Dim(u), map i | 0 <= i < Dim(u) :: u[i] + v[i])
    }

    lemma lemma_GetAdd()
        ensures forall u, v, i | Dim(u) == Dim(v) && 0 <= i < Dim(Add(u, v)) ::
            Get(Add(u, v), i) == Get(u, i) + Get(v, i)
    {}

    function Scale(alpha: real, v: T): T
        ensures Dim(Scale(alpha, v)) == Dim(v)

    {
        MapToSeq(Dim(v), map i | 0 <= i < Dim(v) :: alpha * v[i])
    }

    lemma lemma_GetScale()
        ensures forall alpha, v, i | 0 <= i < Dim(Scale(alpha, v)) ::
            Get(Scale(alpha, v), i) == alpha * Get(v, i)
    {}

    function ZipMul(alphas: seq<real>, betas: seq<real>): (gammas: seq<real>)
        requires |alphas| == |betas|
        ensures |gammas| == |alphas|
    {
        ZipWith((x, y) => x * y, alphas, betas)
    }

    function Dot(u: T, v: T): real
        requires Dim(u) == Dim(v)
    {
        SumReals(ZipMul(u, v))
    }

    lemma lemma_GetAuto()
        ensures forall v, i {:trigger Get(FromSeq(v), i)} | 0 <= i < |v| :: Get(FromSeq(v), i) == v[i]
        ensures forall v, i {:trigger ToSeq(v)[i]} | 0 <= i < Dim(v) :: Get(v, i) == ToSeq(v)[i]
        ensures forall alpha, v, i | 0 <= i < Dim(Scale(alpha, v)) ::
            Get(Scale(alpha, v), i) == alpha * Get(v, i)
        ensures forall u, v, i | Dim(u) == Dim(v) && 0 <= i < Dim(Add(u, v)) ::
            Get(Add(u, v), i) == Get(u, i) + Get(v, i)
    {}

    predicate SeqDim(n: nat, vs: seq<T>)
    {
        forall v | v in vs :: Dim(v) == n
    }

    predicate SeqSameDim(vs: seq<T>)
    {
        forall u, v | u in vs && v in vs :: Dim(u) == Dim(v)
    }


    predicate IsetDim(n: nat, vs: iset<T>)
    {
        forall v | v in vs :: Dim(v) == n
    }

    predicate IsetSameDim(vs: iset<T>)
    {
        forall u, v | u in vs && v in vs :: Dim(u) == Dim(v)
    }


    function Origin(n: nat): T
        ensures Dim(Origin(n)) == n
    {
        Repeat(n, 0.0)
    }

    function SumVectors(n: nat, vs: seq<T>): (ans: T)
        requires SeqDim(n, vs)
        ensures Dim(ans) == n
    {
        if vs == [] then
            Origin(n)
        else
            Add(vs[0], SumVectors(n, vs[1..]))
    }

    function ScaleAll(n: nat, alphas: seq<real>, vs: seq<T>): (ans: seq<T>)
        requires |alphas| == |vs| && SeqDim(n, vs)
        ensures |ans| == |alphas| && SeqDim(n, ans)
    {
        MapToSeq(|vs|, map i | 0 <= i < |vs| :: Scale(alphas[i], vs[i]))
    }

    function LinearCombine(n: nat, alphas: seq<real>, vs: seq<T>): (ans: T)
        requires |alphas| == |vs| && SeqDim(n, vs)
        ensures Dim(ans) == n
    {
        SumVectors(n, ScaleAll(n, alphas, vs))
    }

    function Span(n: nat, vs: seq<T>): (ans: iset<T>)
        requires SeqDim(n, vs)
        ensures IsetDim(n, ans)
    {
        iset alphas | |alphas| == |vs| :: LinearCombine(n, alphas, vs)
    }

    predicate LinearlyIndependent(vs: seq<T>)
        requires SeqSameDim(vs)
    {
        || vs == []
        || var n := Dim(vs[0]);
            forall alphas |
                && |alphas| == |vs|
                && LinearCombine(n, alphas, vs) == Origin(n) ::
                forall alpha | alpha in alphas :: alpha == 0.0
    }

    lemma lemma_SpanRemove(n: nat, vs: seq<T>, i: int)
        requires SeqDim(n, vs)
        requires 0 < i < |vs| && vs[i] in Span(n, vs[..i])
        ensures Span(n, vs[..i] + vs[i+1..]) == Span(n, vs)
    {
        assume false;
    }

    function LargestSuchThat(lo: int, hi: int, p: int --> bool): (i: int)
        requires forall i | lo <= i < hi :: p.requires(i)
        requires exists i | lo <= i < hi :: p(i)
        decreases hi - lo
        ensures lo <= i < hi && p(i)
        // 1ensures forall i' | lo <= i' < hi && p(i') :: i' <= i
    {
        if p(hi-1) then hi-1
        else LargestSuchThat(lo, hi-1, p)
    }

    lemma lemma_LargestSuchThatAllHigher(lo: int, hi: int, p: int --> bool)
        requires forall i | lo <= i < hi :: p.requires(i)
        requires exists i | lo <= i < hi :: p(i)
        decreases hi - lo
        ensures forall j | LargestSuchThat(lo, hi, p) < j < hi :: !p(j)
    {}

    lemma lemma_ScaleOrigin(alpha: real, v: T)
        requires Scale(alpha, v) == Origin(Dim(v))
        ensures alpha == 0.0 || v == Origin(Dim(v))
    {}

    lemma lemma_ScaleZero(v: T)
        ensures Scale(0.0, v) == Origin(Dim(v))
    {}

    predicate AllZeroAfter(i: int, alphas: seq<real>)
    {
        forall j | 0 <= i < j < |alphas| :: alphas[j] == 0.0
    }

    lemma lemma_ScaleAllAllZeroAfter(n: nat, i: int, alphas: seq<real>, vs: seq<T>)
        requires SeqDim(n, vs) && |alphas| == |vs|
        requires 0 <= i < |alphas| && AllZeroAfter(i, alphas)
        ensures ScaleAll(n, alphas, vs) ==
                ScaleAll(n, alphas[..i+1], vs[..i+1]) + Repeat(|vs|-i-1, Origin(n))
    {
        forall j | 0 <= j < |alphas|
            ensures ScaleAll(n, alphas, vs)[j] ==
                (ScaleAll(n, alphas[..i+1], vs[..i+1]) + Repeat(|vs|-i-1, Origin(n)))[j]
        {
            if i < j {
                calc {
                    ScaleAll(n, alphas, vs)[j];
                    Scale(alphas[j], vs[j]);
                    { lemma_ScaleZero(vs[j]); }
                    Origin(n);
                    Repeat(|vs|-i-1, Origin(n))[j-i-1];
                    (ScaleAll(n, alphas[..i+1], vs[..i+1]) + Repeat(|vs|-i-1, Origin(n)))[j];
                }
            }
        }
    }

    lemma lemma_SumVectorsRepeatOrigin(n: nat, m: nat)
        ensures SumVectors(n, Repeat(m, Origin(n))) == Origin(n)
    {
        if m != 0 {
            calc {
                SumVectors(n, Repeat(m, Origin(n)));
                SumVectors(n, [Origin(n)] + Repeat(m-1, Origin(n)));
                { lemma_SumVectorsAppend(n, [Origin(n)], Repeat(m-1, Origin(n))); }
                Add(SumVectors(n, [Origin(n)]), SumVectors(n, Repeat(m-1, Origin(n))));
                { lemma_SumVectorsSingleton(n, Origin(n)); }
                Add(Origin(n), SumVectors(n, Repeat(m-1, Origin(n))));
                { lemma_VectorAuto(); }
                SumVectors(n, Repeat(m-1, Origin(n)));
                { lemma_SumVectorsRepeatOrigin(n, m - 1); }
                Origin(n);
            }
        }
    }

    lemma lemma_AddOriginL(v: T)
        ensures Add(Origin(Dim(v)), v) == v
    {
        forall i | 0 <= i < Dim(v)
            ensures Add(Origin(Dim(v)), v)[i] == v[i]
        {
            calc {
                Add(Origin(Dim(v)), v)[i];
                v[i];
            }
        }
    }

    lemma lemma_AddOriginR(v: T)
        ensures Add(v, Origin(Dim(v))) == v
    {
        forall i | 0 <= i < Dim(v)
            ensures Add(v, Origin(Dim(v)))[i] == v[i]
        {}
    }

    lemma lemma_AddAssoc(u: T, v: T, w: T)
        requires Dim(u) == Dim(v) == Dim(w)
        ensures Add(u, Add(v, w)) == Add(Add(u, v), w)
    {
        assert Add(u, Add(v, w)) == Add(Add(u, v), w);
    }

    lemma lemma_SumVectorsAppend(n: nat, us: seq<T>, vs: seq<T>)
        requires SeqDim(n, us) && SeqDim(n, vs)
        ensures SumVectors(n, us + vs) == Add(SumVectors(n, us), SumVectors(n, vs))
    {
        if us == [] {
            lemma_VectorAuto();
        } else {
            calc {
                SumVectors(n, us + vs);
                { assert us + vs == [us[0]] + (us[1..] + vs); }
                Add(us[0], SumVectors(n, us[1..] + vs));
                { lemma_SumVectorsAppend(n, us[1..], vs); }
                Add(us[0], Add(SumVectors(n, us[1..]), SumVectors(n, vs)));
                { lemma_VectorAuto(); }
                Add(SumVectors(n, us), SumVectors(n, vs));
            }
        }
    }

    lemma lemma_SumVectorsSingleton(n: nat, v: T)
        requires Dim(v) == n
        ensures SumVectors(n, [v]) == v
    {
        calc {
            SumVectors(n, [v]);
            Add(v, Origin(n));
            { lemma_VectorAuto(); }
            v;
        }
    }

    lemma lemma_LinearCombineAllZeroAfter(n: nat, alphas: seq<real>, vs: seq<T>, i: int)
        requires |alphas| == |vs| && SeqDim(n, vs)
        requires 0 <= i < |alphas| && AllZeroAfter(i, alphas)
        ensures LinearCombine(n, alphas, vs) == LinearCombine(n, alphas[..i+1], vs[..i+1])
    {
        calc {
            LinearCombine(n, alphas, vs);
            SumVectors(n, ScaleAll(n, alphas, vs));
            { lemma_ScaleAllAllZeroAfter(n, i, alphas, vs); }
            SumVectors(n, ScaleAll(n, alphas[..i+1], vs[..i+1]) +
                          Repeat(|vs| - i - 1, Origin(n)));
            { lemma_SumVectorsAppend(n, ScaleAll(n, alphas[..i+1], vs[..i+1]),
                                        Repeat(|vs| - i - 1, Origin(n))); }
            Add(SumVectors(n, ScaleAll(n, alphas[..i+1], vs[..i+1])),
              SumVectors(n, Repeat(|vs| - i - 1, Origin(n))));
            { lemma_SumVectorsRepeatOrigin(n, |vs| - i - 1); }
            Add(SumVectors(n, ScaleAll(n, alphas[..i+1], vs[..i+1])), Origin(n));
            SumVectors(n, ScaleAll(n, alphas[..i+1], vs[..i+1]));
        }
    }

    lemma lemma_LinearCombineAllZeroButFirst(n: nat, alphas: seq<real>, vs: seq<T>)
        requires SeqDim(n, vs) && |alphas| == |vs| > 0
        requires LinearCombine(n, alphas, vs) == Origin(n)
        requires AllZeroAfter(0, alphas) && alphas[0] != 0.0
        ensures vs[0] == Origin(n)
    {
        calc ==> {
            true;
            calc {
                LinearCombine(n, alphas, vs);
                { lemma_LinearCombineAllZeroAfter(n, alphas, vs, 0); }
                LinearCombine(n, alphas[..1], vs[..1]);
                { assert alphas[..1] == [alphas[0]];
                  assert vs[..1] == [vs[0]]; }
                SumVectors(n, ScaleAll(n, [alphas[0]], [vs[0]]));
                Scale(alphas[0], vs[0]);
            }
            LinearCombine(n, alphas, vs) == Scale(alphas[0], vs[0]);
            Scale(alphas[0], vs[0]) == Origin(n);
            { lemma_ScaleOrigin(alphas[0], vs[0]); }
            vs[0] == Origin(n);
        }
    }

    lemma lemma_AddOriginLAuto()
        ensures forall n, v {:trigger Add(Origin(n), v)} | n == Dim(v) :: Add(Origin(n), v) == v
    {
        forall v
        {
            lemma_AddOriginL(v);
        }
    }

    lemma lemma_AddOriginRAuto()
        ensures forall n, v {:trigger Add(v, Origin(n))} | n == Dim(v) :: Add(v, Origin(n)) == v
    {
        forall v
        {
            lemma_AddOriginR(v);
        }

    }

    lemma lemma_AddAssocAuto()
        ensures forall u, v, w {:trigger Add(u, Add(v, w))} {:trigger Add(Add(u, v), w)}
                 | Dim(u) == Dim(v) == Dim(w)
                 :: Add(u, Add(v, w)) == Add(Add(u, v), w)
    {
        forall u, v, w | Dim(u) == Dim(v) == Dim(w)
        {
            lemma_AddAssoc(u, v, w);
        }
    }

    lemma lemma_VectorAuto()
        ensures (forall n, v {:trigger Add(Origin(n), v)} | n == Dim(v) :: Add(Origin(n), v) == v)
        ensures (forall n, v {:trigger Add(v, Origin(n))} | n == Dim(v) :: Add(v, Origin(n)) == v)
        ensures (forall u, v, w {:trigger Add(u, Add(v, w))} {:trigger Add(Add(u, v), w)}
                 | Dim(u) == Dim(v) == Dim(w)
                 :: Add(u, Add(v, w)) == Add(Add(u, v), w))
    {
        lemma_AddOriginLAuto();
        lemma_AddOriginRAuto();
        lemma_AddAssocAuto();
    }

    lemma lemma_AddNegate(alpha: real, v: T)
        ensures Add(Scale(alpha, v), Scale(-alpha, v)) == Origin(Dim(v))
    {}

    lemma lemma_AddNegateAuto()
        ensures forall alpha, v {:trigger Scale(alpha, v)} ::
            Add(Scale(alpha, v), Scale(-alpha, v)) == Origin(Dim(v))
    {
        forall alpha: real, v: T
            ensures Add(Scale(alpha, v), Scale(-alpha, v)) == Origin(Dim(v))
        {
            lemma_AddNegate(alpha, v);
        }
    }

    lemma lemma_ScaleInverse(alpha: real, v: T)
        requires alpha != 0.0
        ensures Scale(1.0/alpha, Scale(alpha, v)) == v
    {
        forall i | 0 <= i < |v|
            ensures Scale(1.0/alpha, Scale(alpha, v))[i] == v[i]
        {
            lemma_GetAuto();
            calc {
                Scale(1.0/alpha, Scale(alpha, v))[i];
                Get(Scale(1.0/alpha, Scale(alpha, v)), i);
                (1.0 / alpha) * (alpha * Get(v, i));
                ((1.0 / alpha) * alpha) * Get(v, i);
                Get(v, i);
                v[i];
            }
        }
    }

    lemma lemma_ScaleInverseAuto()
        ensures forall alpha, v | alpha != 0.0 :: Scale(1.0/alpha, Scale(alpha, v)) == v
    {
        forall alpha, v: T | alpha != 0.0
            ensures Scale(1.0/alpha, Scale(alpha, v)) == v
        {
            lemma_ScaleInverse(alpha, v);
        }
    }

    function GetAll(n: nat, vs: seq<T>, i: int): seq<real>
        requires SeqDim(n, vs) && 0 <= i < n
    {
        Map(v requires Dim(v) == n => Get(v, i), vs)
    }

    lemma lemma_GetSumVectors(n: nat, vs: seq<T>, i: int)
        requires SeqDim(n, vs) && 0 <= i < n
        ensures Get(SumVectors(n, vs), i) == SumReals(GetAll(n, vs, i))
    {
        if vs != [] {
            calc {
                Get(SumVectors(n, vs), i);
                Get(Add(vs[0], SumVectors(n, vs[1..])), i);
                Get(vs[0], i) + Get(SumVectors(n, vs[1..]), i);
                { lemma_GetSumVectors(n, vs[1..], i); }
                Get(vs[0], i) + SumReals(GetAll(n, vs[1..], i));
                { assert GetAll(n, vs[1..], i) == GetAll(n, vs, i)[1..]; }
                Get(vs[0], i) + SumReals(GetAll(n, vs, i)[1..]);
                SumReals(GetAll(n, vs, i));
            }
        }
    }

    lemma lemma_GetAllScaleAll(n: nat, alphas: seq<real>, vs: seq<T>, i: int)
        requires SeqDim(n, vs) && |alphas| == |vs| && 0 <= i < n
        ensures GetAll(n, ScaleAll(n, alphas, vs), i) ==
                ZipMul(alphas, GetAll(n, vs, i))
    {
        forall j | 0 <= j < |vs|
            ensures GetAll(n, ScaleAll(n, alphas, vs), i)[j] ==
                    ZipMul(alphas, GetAll(n, vs, i))[j]
        {
            calc {
                GetAll(n, ScaleAll(n, alphas, vs), i)[j];
                Get(ScaleAll(n, alphas, vs)[j], i);
                Get(Scale(alphas[j], vs[j]), i);
                alphas[j] * Get(vs[j], i);
                alphas[j] * GetAll(n, vs, i)[j];
                ZipMul(alphas, GetAll(n, vs, i))[j];
            }
        }
    }

    lemma lemma_ZipMulUnroll(alphas: seq<real>, betas: seq<real>)
        requires |alphas| == |betas| > 0
        ensures ZipMul(alphas, betas) == [alphas[0] * betas[0]] + ZipMul(alphas[1..], betas[1..])
    {}

    lemma lemma_SumRealsZipMulRepeat(alpha: real, alphas: seq<real>)
        ensures SumReals(ZipMul(Repeat(|alphas|, alpha), alphas)) ==
                alpha * SumReals(alphas)
    {
        if alphas != [] {
            calc {
                SumReals(ZipMul(Repeat(|alphas|, alpha), alphas));
                { var l := Repeat(|alphas|, alpha);
                  lemma_ZipMulUnroll(l, alphas);
                }
                SumReals([alpha * alphas[0]] + ZipMul(Repeat(|alphas[1..]|, alpha), alphas[1..]));
                alpha * alphas[0] + SumReals(ZipMul(Repeat(|alphas[1..]|, alpha), alphas[1..]));
                { lemma_SumRealsZipMulRepeat(alpha, alphas[1..]); }
                alpha * alphas[0] + alpha * SumReals(alphas[1..]);
                alpha * (alphas[0] + SumReals(alphas[1..])); 
                alpha * SumReals(alphas);
            }
        }
    }

    lemma lemma_ScaleSumVectors(n: nat, alpha: real, vs: seq<T>)
        requires SeqDim(n, vs)
        ensures Scale(alpha, SumVectors(n, vs)) ==
                SumVectors(n, ScaleAll(n, Repeat(|vs|, alpha), vs))
    {
        forall i | 0 <= i < n
            ensures Scale(alpha, SumVectors(n, vs))[i] ==
                    SumVectors(n, ScaleAll(n, Repeat(|vs|, alpha), vs))[i]
        {
            calc {
                Scale(alpha, SumVectors(n, vs))[i];
                Get(Scale(alpha, SumVectors(n, vs)), i);
                { lemma_GetScale(); }
                alpha * Get(SumVectors(n, vs), i);
                { lemma_GetSumVectors(n, vs, i); }
                alpha * SumReals(GetAll(n, vs, i));
                { lemma_SumRealsZipMulRepeat(alpha, GetAll(n, vs, i)); }
                SumReals(ZipMul(Repeat(|vs|, alpha), GetAll(n, vs, i)));
                { lemma_GetAllScaleAll(n, Repeat(|vs|, alpha), vs, i); }
                SumReals(GetAll(n, ScaleAll(n, Repeat(|vs|, alpha), vs), i));
                { lemma_GetSumVectors(n, ScaleAll(n, Repeat(|vs|, alpha), vs), i); }
                Get(SumVectors(n, ScaleAll(n, Repeat(|vs|, alpha), vs)), i);
                SumVectors(n, ScaleAll(n, Repeat(|vs|, alpha), vs))[i];
            }
        }
    }

    function Mul(alpha: real, beta: real): real
    {
        alpha * beta
    }

    function MulAll(alpha: real, alphas: seq<real>): seq<real>
    {
        Map(x => alpha * x, alphas)
    }

    lemma lemma_ScaleScale(alpha: real, beta: real, v: T)
        ensures Scale(alpha, Scale(beta, v)) == Scale(Mul(alpha, beta), v)
    {
        forall i | 0 <= i < |v|
            ensures Scale(alpha, Scale(beta, v))[i] == Scale(Mul(alpha, beta), v)[i]
        {
            calc {
                Scale(alpha, Scale(beta, v))[i];
                alpha * (beta * v[i]);
                (alpha * beta) * v[i];
                Scale(Mul(alpha, beta), v)[i];
            }
        }
    }

    lemma lemma_ScaleAllScaleAll(n: nat, alphas: seq<real>, betas: seq<real>, vs: seq<T>)
        requires SeqDim(n, vs) && |alphas| == |betas| == |vs|
        ensures ScaleAll(n, alphas, ScaleAll(n, betas, vs)) ==
                ScaleAll(n, ZipMul(alphas, betas), vs)
    {
        forall i | 0 <= i < |vs|
            ensures ScaleAll(n, alphas, ScaleAll(n, betas, vs))[i] ==
                    ScaleAll(n, ZipMul(alphas, betas), vs)[i]
        {
            var alpha, beta, v := alphas[i], betas[i], vs[i];
            calc {
                ScaleAll(n, alphas, ScaleAll(n, betas, vs))[i];
                Scale(alpha, Scale(beta, v));
                { lemma_ScaleScale(alpha, beta, v); }
                Scale(Mul(alpha, beta), v);
                { assert ZipMul(alphas, betas)[i] == alpha * beta; }
                Scale(ZipMul(alphas, betas)[i], v);
                ScaleAll(n, ZipMul(alphas, betas), vs)[i];
            }
        }

    }

    lemma lemma_ZipMulRepeat(alpha: real, alphas: seq<real>)
        ensures ZipMul(Repeat(|alphas|, alpha), alphas) == MulAll(alpha, alphas)
    {
        forall i | 0 <= i < |alphas|
            ensures ZipMul(Repeat(|alphas|, alpha), alphas)[i] == MulAll(alpha, alphas)[i]
        {
            calc {
                ZipMul(Repeat(|alphas|, alpha), alphas)[i];
                Repeat(|alphas|, alpha)[i] * alphas[i];
                alpha * alphas[i];
                MulAll(alpha, alphas)[i];
            }
        }
    }

    lemma lemma_ScaleLinearCombine(n: nat, alpha: real, alphas: seq<real>, vs: seq<T>)
        requires SeqDim(n, vs) && |alphas| == |vs|
        ensures Scale(alpha, LinearCombine(n, alphas, vs)) ==
                LinearCombine(n, MulAll(alpha, alphas), vs)
    {
        calc {
            Scale(alpha, LinearCombine(n, alphas, vs));
            Scale(alpha, SumVectors(n, ScaleAll(n, alphas, vs)));
            { lemma_ScaleSumVectors(n, alpha, ScaleAll(n, alphas, vs)); }
            SumVectors(n, ScaleAll(n, Repeat(|vs|, alpha), ScaleAll(n, alphas, vs)));
            { lemma_ScaleAllScaleAll(n, Repeat(|vs|, alpha), alphas, vs); }
            SumVectors(n, ScaleAll(n, ZipMul(Repeat(|vs|, alpha), alphas), vs));
            { lemma_ZipMulRepeat(alpha, alphas); }
            LinearCombine(n, MulAll(alpha, alphas), vs);
        }
    }

    lemma lemma_ScaleLinearCombineAuto()
        ensures forall n: nat, alpha: real, alphas: seq<real>, vs: seq<T>
            | SeqDim(n, vs) && |alphas| == |vs|
            :: Scale(alpha, LinearCombine(n, alphas, vs)) ==
              LinearCombine(n, MulAll(alpha, alphas), vs)
    {
        forall n: nat, alpha: real, alphas: seq<real>, vs: seq<T>
            | SeqDim(n, vs) && |alphas| == |vs|
            ensures Scale(alpha, LinearCombine(n, alphas, vs)) ==
              LinearCombine(n, MulAll(alpha, alphas), vs)
        {
            lemma_ScaleLinearCombine(n, alpha, alphas, vs);
        }
    }

    lemma lemma_EstablishInSpan(n: nat, alphas: seq<real>, vs: seq<T>, alpha: real, v: T)
        requires SeqDim(n, vs) && |alphas| == |vs| > 0 && Dim(v) == n
        requires Add(LinearCombine(n, alphas, vs), Scale(alpha, v)) == Origin(n)
        requires alpha != 0.0
        ensures v in Span(n, vs)
    {
        calc ==> {
            true;
            Add(LinearCombine(n, alphas, vs), Scale(alpha, v)) == Origin(n);
            Add(Add(LinearCombine(n, alphas, vs), Scale(alpha, v)), Scale(-alpha, v)) ==
              Add(Origin(n), Scale(-alpha, v));
            { lemma_VectorAuto(); }
            Add(LinearCombine(n, alphas, vs), Add(Scale(alpha, v), Scale(-alpha, v))) ==
              Scale(-alpha, v);
            { lemma_AddNegateAuto(); }
            Add(LinearCombine(n, alphas, vs), Origin(n)) == Scale(-alpha, v);
            { lemma_VectorAuto(); }
            LinearCombine(n, alphas, vs) == Scale(-alpha, v);
            Scale(-1.0/alpha, LinearCombine(n, alphas, vs)) ==
              Scale(-1.0/alpha, Scale(-alpha, v));
            { lemma_ScaleInverseAuto(); }
            Scale(-1.0/alpha, LinearCombine(n, alphas, vs)) == v;
            { lemma_ScaleLinearCombine(n, -1.0/alpha, alphas, vs); }
            LinearCombine(n, MulAll(-1.0/alpha, alphas), vs) == v;
        }
    }

    lemma lemma_ScaleAllUnroll(n: nat, alphas: seq<real>, vs: seq<T>)
        requires SeqDim(n, vs) && |alphas| == |vs| > 0
        ensures ScaleAll(n, alphas, vs) ==
                ScaleAll(n, ButLast(alphas), ButLast(vs)) +
                [Scale(Last(alphas), Last(vs))]
    {}


    lemma lemma_LinearCombineUnroll(n: nat, alphas: seq<real>, vs: seq<T>)
        requires SeqDim(n, vs) && |alphas| == |vs| > 0
        ensures LinearCombine(n, alphas, vs) ==
                Add(LinearCombine(n, ButLast(alphas), ButLast(vs)),
                    Scale(Last(alphas), Last(vs)))
    {
        calc {
            LinearCombine(n, alphas, vs);
            SumVectors(n, ScaleAll(n, alphas, vs));
            { lemma_ScaleAllUnroll(n, alphas, vs); }
            SumVectors(n, ScaleAll(n, ButLast(alphas), ButLast(vs)) +
                          [Scale(Last(alphas), Last(vs))]);
            { lemma_SumVectorsAppend(n, ScaleAll(n, ButLast(alphas), ButLast(vs)),
                                    [Scale(Last(alphas), Last(vs))]); }
            Add(SumVectors(n, ScaleAll(n, ButLast(alphas), ButLast(vs))),
                SumVectors(n, [Scale(Last(alphas), Last(vs))]));
            { lemma_SumVectorsSingleton(n, Scale(Last(alphas), Last(vs))); }
            Add(LinearCombine(n, ButLast(alphas), ButLast(vs)),
                Scale(Last(alphas), Last(vs)));
        }
    }

    lemma lemma_ShrinkLinearDependent(n: nat, alphas: seq<real>, vs: seq<T>) returns (i: int)
        requires SeqDim(n, vs) && |alphas| == |vs| > 0 && vs[0] != Origin(n)
        requires exists i | 0 <= i < |alphas| :: alphas[i] != 0.0
        requires LinearCombine(n, alphas, vs) == Origin(n)
        ensures
            && 0 < i < |vs|
            && vs[i] in Span(n, vs[..i])
            && Span(n, vs[..i] + vs[i+1..]) == Span(n, vs)
    {
        var p := i requires 0 < i < |vs| => alphas[i] != 0.0;
        assert exists i | 0 < i < |vs| :: p(i) by {
            if forall j | 0 < j < |vs| :: !p(j) {
                assert forall j | 0 < j < |vs| :: p(j) <==> alphas[j] != 0.0;
                var i :| 0 <= i < |alphas| && alphas[i] != 0.0;
                assert i == 0;
                lemma_LinearCombineAllZeroButFirst(n, alphas, vs);
            }
        }
        i := LargestSuchThat(1, |vs|, p);
        assert AllZeroAfter(i, alphas) by {
            assert forall j | 0 < j < |vs| :: p(j) <==> alphas[j] != 0.0;
            lemma_LargestSuchThatAllHigher(1, |vs|, p);
        }
        assert alphas[i] != 0.0;
        assert vs[i] in Span(n, vs[..i]) by {
            calc {
                LinearCombine(n, alphas, vs);
                { lemma_LinearCombineAllZeroAfter(n, alphas, vs, i); }
                LinearCombine(n, alphas[..i+1], vs[..i+1]);
                { lemma_LinearCombineUnroll(n, alphas[..i+1], vs[..i+1]);
                  assert ButLast(alphas[..i+1]) == alphas[..i]; 
                  assert ButLast(vs[..i+1]) == vs[..i];
                }
                Add(LinearCombine(n, alphas[..i], vs[..i]), Scale(alphas[i], vs[i]));
            }
            lemma_EstablishInSpan(n, alphas[..i], vs[..i], alphas[i], vs[i]);
        }
        lemma_SpanRemove(n, vs, i);
    }

}

module VectorSpace {
    import Vector

    export provides T, Valid

    datatype T = T(iset<Vector.T>, nat)

    predicate Valid(t: T)
    {
        var T(V, n) := t;
        && V != iset{}
        && Vector.IsetDim(n, V)
        && (forall u, v | u in V && v in V :: Vector.Add(u, v) in V)
        && (forall alpha, v | v in V :: Vector.Scale(alpha, v) in V)
    }

    predicate IsBasis(t: T, b: seq<Vector.T>)
        requires Valid(t)
    {
        var T(V, n) := t;
        && (forall v | v in b :: v in V)
        && Vector.Span(n, b) == V
        && Vector.LinearlyIndependent(b)
    }


}

module Matrix {
    import opened Prelude
    import Vector

    export provides T

    datatype T = T(data: seq<seq<real>>, inner_dim: nat)

    predicate Valid(m: T)
    {
        forall l | l in m.data :: |l| == m.inner_dim
    }

    function NumRows(m: T): int
    {
        |m.data|
    }

    function NumCols(m: T): int
    {
        m.inner_dim
    }

    function Get(m: T, i: int, j: int): real
        requires Valid(m) && 0 <= i < NumRows(m) && 0 <= j < NumCols(m)
    {
        m.data[i][j]
    }

    function Set(m: T, i: int, j: int, x: real): (m': T)
        requires Valid(m) && 0 <= i < NumRows(m) && 0 <= j < NumCols(m)
        ensures Valid(m') && NumRows(m') == NumRows(m) && NumCols(m') == NumCols(m)
    {
        var d' := m.data[i := m.data[i][j := x]];
        T(d', m.inner_dim)
    }

    lemma lemma_GetSet (m: T, i: int, j: int, x: real)
        requires Valid(m) && 0 <= i < NumRows(m) && 0 <= j < NumCols(m)
        ensures
            var m' := Set(m, i, j, x);
            forall i', j' | 0 <= i' < NumRows(m) && 0 <= j' < NumCols(m) ::
                Get(m', i', j') == if i == i' && j == j' then x else Get(m, i', j')
    {}

    function SwapRows(m: T, r1: int, r2: int): (m': T)
        requires Valid(m) && 0 <= r1 < NumRows(m) && 0 <= r2 < NumRows(m)
        ensures Valid(m') && NumRows(m') == NumRows(m) && NumCols(m') == NumCols(m)
    {
        var d' := m.data[r1 := m.data[r2]][r2 := m.data[r1]];
        T(d', m.inner_dim)
    }

    lemma lemma_GetSwapRows(m: T, r1: int, r2: int)
        requires Valid(m) && 0 <= r1 < NumRows(m) && 0 <= r2 < NumRows(m)
        ensures
            var m' := SwapRows(m, r1, r2);
            forall i, j | 0 <= i < NumRows(m) && 0 <= j < NumCols(m) ::
                Get(m', i, j) == if i == r1 then Get(m, r2, j)
                                 else if i == r2 then Get(m, r1, j)
                                 else Get(m, i, j)
    {}

    lemma lemma_GetRowSwapRows(m: T, r1: int, r2: int)
        requires Valid(m) && 0 <= r1 < NumRows(m) && 0 <= r2 < NumRows(m)
        ensures
            var m' := SwapRows(m, r1, r2);
            forall r | 0 <= r < NumRows(m) ::
                GetRow(m', r) == if r == r1 then GetRow(m, r2)
                                 else if r == r2 then GetRow(m, r1)
                                 else GetRow(m, r)
    {}


    function AddScaledRow(m: T, dst: int, src: int, alpha: real): (m': T)
        requires Valid(m) && 0 <= dst < NumRows(m) && 0 <= src < NumRows(m)
        ensures Valid(m') && NumRows(m') == NumRows(m) && NumCols(m') == NumCols(m)
    {
        var scaled_src := Vector.Scale(alpha, Vector.FromSeq(m.data[src]));
        var v_dst' := Vector.Add(Vector.FromSeq(m.data[dst]), scaled_src);
        var d' := m.data[dst := Vector.ToSeq(v_dst')];
        T(d', m.inner_dim)
    }

    lemma lemma_GetAddScaledRow(m: T, dst: int, src: int, alpha: real)
        requires Valid(m) && 0 <= dst < NumRows(m) && 0 <= src < NumRows(m)
        ensures
            var m' := AddScaledRow(m, dst, src, alpha);
            forall i, j | 0 <= i < NumRows(m) && 0 <= j < NumCols(m) ::
                Get(m', i, j) == if i == dst then Get(m, dst, j) + alpha * Get(m, src, j)
                                 else Get(m, i, j)
    {
        Vector.lemma_GetAuto();
    }

    function GetRow(m: T, i: int): seq<real>
        requires 0 <= i < NumRows(m)
    {
        m.data[i]
    }

    predicate ZeroRow(m: T, i: int)
        requires 0 <= i < NumRows(m)
    {
        forall x | x in GetRow(m, i) :: x == 0.0
    }

    lemma lemma_ZeroRowGetRowEquiv(m1: T, i1: int, m2: T, i2: int)
        requires 0 <= i1 < NumRows(m1) && 0 <= i2 < NumRows(m2)
        requires GetRow(m1, i1) == GetRow(m2, i2)
        ensures ZeroRow(m1, i1) <==> ZeroRow(m2, i2)
    {}

    predicate IsZeroRowBound(m: T, z: int)
        requires Valid(m) && 0 <= z <= NumRows(m)
    {
        forall i | 0 <= i < NumRows(m) ::
              ZeroRow(m, i) <==> i >= z
    }

    predicate IsLeadingColumn(m: T, i: int, j: int)
        requires Valid(m) && 0 <= i < NumRows(m)
    {
        && 0 <= j < NumCols(m)
        && Get(m, i, j) != 0.0
        && (forall j' | 0 <= j' < NumCols(m) && Get(m, i, j') != 0.0 :: j' >= j)
    }

    lemma lemma_LeadingColumnExists(m: T, i: int)
        requires Valid(m) && 0 <= i < NumRows(m) && !ZeroRow(m, i)
        ensures exists j :: IsLeadingColumn(m, i, j)
    {
        var j: int := 0;
        while j < NumCols(m)
            invariant 0 <= j <= NumCols(m)
            invariant forall k | 0 <= k < j :: Get(m, i, k) == 0.0
        {
            if Get(m, i, j) != 0.0 {
                assert IsLeadingColumn(m, i, j);
                return;
            }
            j := j + 1;
        }
        forall x | x in GetRow(m, i)
            ensures x == 0.0
        {
            var k :| 0 <= k < NumCols(m) && GetRow(m, i)[k] == x;
            assert GetRow(m, i)[k] == Get(m, i, k);
        }
        assert ZeroRow(m, i);
    }

    function LeadingColumn(m: T, i: int): (j: int)
        requires Valid(m) && 0 <= i < NumRows(m) && !ZeroRow(m, i)
    {
        lemma_LeadingColumnExists(m, i);
        var j :| IsLeadingColumn(m, i, j);
        j
    }

    predicate EchelonRow(m: T, i: int)
        requires Valid(m) && 0 <= i < NumRows(m)
        requires forall i' | 0 <= i' <= i :: !ZeroRow(m, i')
    {
        var j := LeadingColumn(m, i);
        && Get(m, i, j) == 1.0
        && (i > 0 ==> LeadingColumn(m, i-1) < j)
    }

    predicate RowEchelonForm(m: T)
        requires Valid(m)
    {
        && (exists z | 0 <= z <= NumRows(m) :: IsZeroRowBound(m, z))
        && forall i | 0 <= i < NumRows(m) ::
            !ZeroRow(m, i) ==> EchelonRow(m, i)
    }

    lemma lemma_EstablishNotZeroRow(m: T, i: int, j: int)
        requires Valid(m) && 0 <= i < NumRows(m) && 0 <= j < NumCols(m)
        requires Get(m, i, j) != 0.0
        ensures !ZeroRow(m, i)
    {
        assert Get(m, i, j) in GetRow(m, i);
    }

    ghost method GaussianElimination(mat: T) returns (is_singular: bool, k: int, mat': T)
        requires Valid(mat)
        ensures Valid(mat') // && RowEchelonForm(mat')
    {
        mat' := mat;

        var m := NumRows(mat);
        var n := NumCols(mat);

        k := 0;
        while k < Min(m, n)
            invariant NumRows(mat') == m && NumCols(mat') == n
            invariant Valid(mat')
            invariant 0 <= k <= Min(m, n)
            // invariant forall k' | 0 <= k' < k :: !ZeroRow(mat', k')
        {
            lemma_RangeRange(k, m);
            var i_max := ArgMaxPartial(i requires 0 <= i < m => AbsReal(Get(mat', i, k)),
                Range(k, m));
            lemma_ArgMaxPartialInAuto<int>();
            if Get(mat', i_max, k) == 0.0 {
                is_singular := true;
                return;
            }
            var old_mat' := mat';
            mat' := SwapRows(mat', i_max, k);
            // forall k' | 0 <= k' < k { lemma_ZeroRowGetRowEquiv(mat', k', old_mat', k'); }

            var i := k + 1;
            // lemma_EstablishNotZeroRow(mat', k, k);
            while i < m
                invariant k < i <= m
                invariant NumRows(mat') == m && NumCols(mat') == n
                invariant Valid(mat')
                invariant Get(mat', k, k) != 0.0
                // invariant forall k' | 0 <= k' <= k :: !ZeroRow(mat', k')
            {
                var f := Get(mat', i, k) / Get(mat', k, k);
                old_mat' := mat';
                mat' := AddScaledRow(mat', i, k, - f);
                // forall k' | 0 <= k' <= k { lemma_ZeroRowGetRowEquiv(mat', k', old_mat', k'); }
                i := i + 1;
            }
            k := k + 1;
        }

        /*
        var z := k;
        while z < m
            invariant 0 <= z <= m
            invariant forall k' | 0 <= k' < z :: !ZeroRow(mat', k')
        {
            if ZeroRow(mat', z) { break; }
            z := z + 1;
        }
        assert z < m ==> ZeroRow(mat', z);
        */
        //assert IsZeroRowBound(mat', z);
    }
}
