datatype Option<T> = None | Some(x: T)

function OptionOr<T>(x: Option<T>, y: Option<T>): Option<T>
{
    match x
        case None => y
        case Some(_) => x
}


type Symbol(==)

datatype Q = Forall | Exists

datatype Sort = Bool | Int | UserDeclaredSort(name: Symbol)

datatype Expr =
    | Symbol(name: Symbol)
    | App(name: Symbol, args: seq<Expr>)
    | Quantifier(q: Q, bounds: seq<(Symbol, Sort)>, body: Expr)
    | Let(defs: seq<(Symbol, Expr)>, body: Expr)
    | Num(n: int)

datatype Rank = Rank(args: seq<Sort>, ret: Sort)
type Arity = nat

datatype Declaration =
    | DeclSort(name: Symbol, arity: Arity)
    | DeclFun(name: Symbol, rank: Rank)

datatype Assertion = Formula(f: Expr) | Declaration(d: Declaration)

type Level = seq<Assertion>

function LookupSortInLevel(name: Symbol, l: Level): Option<Arity>
{
    if l == [] then
        None
    else if l[0].Declaration? && l[0].d.DeclSort? && l[0].d.name == name then
        Some(l[0].d.arity)
    else
        LookupSortInLevel(name, l[1..])
}

function LookupFunctionInLevel(name: Symbol, l: Level): Option<Rank>
{
    if l == [] then
        None
    else if l[0].Declaration? && l[0].d.DeclFun? && l[0].d.name == name then
        Some(l[0].d.rank)
    else
        LookupFunctionInLevel(name, l[1..])
}

function Reverse<A>(s: seq<A>): seq<A>
{
    if s == [] then
        []
    else
        s[1..] + [s[0]]
}

function Map<A, B>(f: imap<A, B>, s: seq<A>): seq<B>
    requires forall x | x in s :: x in f
{
    if s == [] then
        []
    else
        [f[s[0]]] + Map(f, s[1..])
}

function AddBoundVarsToLevel(bounds: seq<(Symbol, Sort)>, l: Level): Level
{
    Map(imap p: (Symbol, Sort) | true :: Declaration(DeclFun(p.0, Rank([], p.1))), Reverse(bounds))
}


type Stack = seq<Level>

function LookupSortInStack(name: Symbol, s: Stack): Option<Arity>
{
    if s == [] then
        None
    else OptionOr(LookupSortInLevel(name, s[0]), LookupSortInStack(name, s[1..]))
}

function LookupFunctionInStack(name: Symbol, s: Stack): Option<Rank>
{
    if s == [] then
        None
    else OptionOr(LookupFunctionInLevel(name, s[0]), LookupFunctionInStack(name, s[1..]))
}

function AddBoundVarsToStack(bounds: seq<(Symbol, Sort)>, s: Stack): Stack
    requires |s| > 0
{
    [AddBoundVarsToLevel(bounds, s[0])] + s[1..]
}

function Range(lo: int, length: nat): seq<int>
    decreases length
{
    if length == 0 then
        []
    else
        [lo] + Range(lo + 1, length - 1)
}

function HasSort(stack: Stack, e: Expr): Option<Sort>
    requires |stack| > 0
    decreases e
{
    match e
        case Symbol(name) =>
            var o := LookupFunctionInStack(name, stack);
            if o.Some? && o.x.args == [] then
                Some(o.x.ret)
            else
                None
        case App(name, args) =>
            var o := LookupFunctionInStack(name, stack);
            if && o.Some?
               && |o.x.args| == |args|
               && forall i | 0 <= i < |args| :: HasSort(stack, args[i]) == Some(o.x.args[i])
            then
                Some(o.x.ret)
            else
                None
        case Quantifier(q, bs, e) =>
            if HasSort(AddBoundVarsToStack(bs, stack), e) == Some(Bool) then
                Some(Bool)
            else
                None
        case Let(defs, e) =>
            match DefsHaveSorts(stack, defs) {
                case None => None
                case Some(bs) =>
                    HasSort(AddBoundVarsToStack(bs, stack), e)
            }
        case Num(_) => Some(Int)
}

function DefsHaveSorts(stack: Stack, defs: seq<(Symbol, Expr)>): Option<seq<(Symbol, Sort)>>
    requires |stack| > 0
    decreases defs
{
    if defs == [] then
        Some([])
    else
        match HasSort(stack, defs[0].1)
            case None => None
            case Some(sort) =>
                match DefsHaveSorts(stack, defs[1..])
                    case None => None
                    case Some(sorts) => Some([(defs[0].0, sort)] + sorts)
}


predicate StackValid(s: Stack)
{
    true
}

class Solver {
    ghost var stack: Stack

    predicate Valid()
        reads this
    {
        StackValid(stack)
    }

}
