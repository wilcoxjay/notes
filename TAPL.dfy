datatype Ty = Bool | Arrow(ty1: Ty, ty2: Ty)

datatype Exp =
    | Var(n: int)
    | App(e1: Exp, e2: Exp)
    | Abs(ty: Ty, body: Exp)
    | Const(b: bool)
    | If(e1: Exp, e2: Exp, e3: Exp)

predicate Value(e: Exp)
{
    e.Abs? || e.Const?
}

// Shift all variables >= c by d
function Shift'(c: nat, d: int, e: Exp): Exp
{
    match e
        case Var(n) => Var(if n >= c then n + d else n)
        case App(e1, e2) => App(Shift(c, d, e1), Shift(c, d, e2))
        case Abs(ty, e) => Abs(ty, Shift(c, d, e))
}

function Shift(d: int, e: Exp): Exp
{
    Shift'(0, d, e)
}

function Subst(from: nat, to: Exp, e: Exp): Exp
{
    match e
        case Var(n) => if n == from then to else e
        case App(e1, e2) => App(Subst(from, to, e1), Subst(from, to, e2))
        case Abs(ty, e) => Abs(ty, Subst(from+1, Shift(1, to), e))
}

function Step(e: Exp): Exp
{
  match e
    case Var(_) =>
    case App(e1, e2) =>
        if Value(e1) then
            if Value(e2) then
                if e1.Abs? then
                    e' == Subst(0, e2, e1.body)
                else
                    false
            else




}
