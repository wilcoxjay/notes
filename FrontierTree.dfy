// RUN: /compile:0 /nologo /noNLarith /noCheating:1  /rlimit:1000000

datatype BT<A> = Tip(data: A) | Node(left: BT<A>, right: BT<A>)

class IO<T> {
    var alpha: seq<T>, omega: seq<T>;

    method Input() returns (x: T)
        requires !EOF() //alpha != []
        modifies this
        ensures omega == old(omega)
        ensures old(alpha) == [x] + alpha
    {
        x, alpha := alpha[0], alpha[1..];
    }

    method Output(x: T)
        modifies this
        ensures alpha == old(alpha)
        ensures omega == old(omega) + [x]
    {
        omega := omega + [x];
    }

    method Rewrite()
        modifies this
        ensures omega == []
        ensures alpha == old(alpha)
    {
        omega := [];
    }

    predicate method EOF() reads this { alpha == [] }

}

method Main()
{
    var tree: BT<int>;
    tree := Tip(1);
    var io: IO<int>;
    io := new IO<int>;
    FrontierIter(tree, io);
    print io.omega;

    io.Rewrite();
    tree := Node(tree, Tip(2));
    FrontierIter(tree, io);
    print io.omega;
}

function Frontier<T>(tree: BT<T>): seq<T>
{
    match tree {
        case Tip(n) => [n]
        case Node(left, right) => Frontier(left) + Frontier(right)
    }
}

function Size<T>(tree: BT<T>): nat
{
    match tree
        case Tip(_) => 1
        case Node(l, r) => Size(l) + Size(r) + 1
}

function TotalSize<T>(stack: seq<BT<T>>): nat
{
    if stack == [] then
        0
    else
        Size(stack[0]) + TotalSize(stack[1..])
}

function StackFrontier<T>(stack: seq<BT<T>>): seq<T>
{
    if stack == [] then
        []
    else
        Frontier(stack[0]) + StackFrontier(stack[1..])
}

method FrontierIter<T>(tree: BT<T>, io: IO<T>)
    requires io != null
    modifies io
    ensures io.omega == old(io.omega) + Frontier(tree)
{
    var stack: seq<BT<T>>;
    var current: BT<T>;

    stack := [tree];

    while stack != []
        invariant io.omega + StackFrontier(stack) == old(io.omega) + Frontier(tree)
        decreases TotalSize(stack)
    {
        ghost var previous_stack := stack;
        assert io.omega + StackFrontier(previous_stack) == old(io.omega) + Frontier(tree);
        current, stack := stack[0], stack[1..];
        match current {
            case Tip(x) => io.Output(x);
            case Node(l, r) => {
                stack := [l, r] + stack;
                assert TotalSize(stack) == Size(l) + (Size(r) + TotalSize(stack[2..]));

                calc {
                    StackFrontier(stack);
                    == Frontier(l) + (Frontier(r) + StackFrontier(stack[2..]));
                    == StackFrontier(previous_stack);
                }
            }
        }
    }
}
