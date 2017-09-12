module M1 {

    datatype expr = Const(n: int) | Plus(e1: expr, e2: expr)
    
    function interp_expr(e: expr): int {
        match e
        case Const(n) => n
        case Plus(e1, e2) => interp_expr(e1) + interp_expr(e2)
    }
    
    datatype instr = Push(n: int) | Add
    
    type stack = seq<int>
    
    function exec_instr(i: instr, s: stack): stack
    {
        match i
        case Push(n) => [n] + s
        case Add =>
            if |s| < 2 then
                s
            else
                [s[0] + s[1]] + s[2..]
    }
    
    type prog = seq<instr>
    
    function exec_prog(p: prog, s: stack): stack
    {
        if p == [] then
            s
        else
            var s' := exec_instr(p[0], s);
            exec_prog(p[1..], s')
    }
    
    function compile(e: expr): prog
    {
        match e
        case Const(n) => [Push(n)]
        case Plus(e1, e2) => compile(e1) + compile(e2) + [Add]
    }
    
    lemma exec_prog_append(p1: prog, p2: prog, s: stack)
        ensures exec_prog(p1 + p2, s) == exec_prog(p2, exec_prog(p1, s))
    {
        if p1 != [] {
            assert (p1 + p2)[1..] == p1[1..] + p2;
        }
    }

    lemma compile_correct_stack(e: expr, s: stack)
        ensures exec_prog(compile(e), s) == [interp_expr(e)] + s
    {
        match e
            case Const(n) => {}
            case Plus(e1, e2) =>
                calc {
                    exec_prog(compile(e), s);
                    == exec_prog(compile(e1) + compile(e2) + [Add], s);
                    == { exec_prog_append(compile(e1) + compile(e2), [Add], s); }
                       exec_prog([Add], exec_prog(compile(e1) + compile(e2), s));
                    == { exec_prog_append(compile(e1),  compile(e2), s); }
                       exec_prog([Add], exec_prog(compile(e2), exec_prog(compile(e1), s)));
                    == [interp_expr(e2) + interp_expr(e1)] + s;
                }
    }

    lemma compile_correct(e: expr)
        ensures exec_prog(compile(e), []) == [interp_expr(e)]
    {
        compile_correct_stack(e, []);
    }
}


module M2 {

    datatype expr = Const(n: int) | Plus(e1: expr, e2: expr)
    
    function interp_expr(e: expr): int {
        match e
        case Const(n) => n
        case Plus(e1, e2) => interp_expr(e1) + interp_expr(e2)
    }
    
    datatype instr = Push(n: int) | Add
    
    type stack = seq<int>
    
    function instr_stack_depth_requirement(i: instr): nat
    {
        match i
        case Push(_) => 0
        case Add => 2
    }

    function instr_stack_depth_effect(i: instr): int
    {
        match i
        case Push(_) => 1
        case Add => -1

    }

    predicate instr_stack_safe(i: instr, n: int)
    {
        && 0 <= n
        && instr_stack_depth_requirement(i) <= n
    }

    function exec_instr(i: instr, s: stack): stack
        requires instr_stack_safe(i, |s|)
    {
        match i
        case Push(n) => [n] + s
        case Add => [s[0] + s[1]] + s[2..]
    }
    
    type prog = seq<instr>
    

    predicate prog_stack_safe(p: prog, depth: int)
    {
        && 0 <= depth
        && p != [] ==>
            && instr_stack_safe(p[0], depth)
            && var depth' := depth + instr_stack_depth_effect(p[0]);
              prog_stack_safe(p[1..], depth')
    }

    function prog_stack_depth_effect(p: prog): int
    {
        if p == [] then
            0
        else
            instr_stack_depth_effect(p[0]) + prog_stack_depth_effect(p[1..])
    }

    lemma prog_stack_depth_effect_execute(p: prog, s: stack)
        requires prog_stack_safe(p, |s|)
        ensures |exec_prog(p, s)| == |s| + prog_stack_depth_effect(p)
    {}

    function exec_prog(p: prog, s: stack): stack
        requires prog_stack_safe(p, |s|)
    {
        if p == [] then
            s
        else
            var s' := exec_instr(p[0], s);
            exec_prog(p[1..], s')
    }
    
    function compile(e: expr): prog
    {
        match e
        case Const(n) => [Push(n)]
        case Plus(e1, e2) => compile(e1) + compile(e2) + [Add]
    }
    
    lemma prog_stack_safe_append_elim(p1: prog, p2: prog, s: stack)
        requires prog_stack_safe(p1 + p2, |s|)
        ensures prog_stack_safe(p1, |s|)
        ensures prog_stack_safe(p2, |exec_prog(p1, s)|)
    {
        if p1 != [] {
            assert (p1 + p2)[1..] == p1[1..] + p2;
            prog_stack_safe_append_elim(p1[1..], p2, exec_instr(p1[0], s));
        }
    }

    lemma prog_stack_safe_append_intro(p1: prog, p2: prog, n: int)
        requires prog_stack_safe(p1, n)
        requires prog_stack_safe(p2, n + prog_stack_depth_effect(p1))
        ensures prog_stack_safe(p1 + p2, n)
    {
        if p1 != [] {
            assert (p1 + p2)[1..] == p1[1..] + p2;
            prog_stack_safe_append_intro(p1[1..], p2, instr_stack_depth_effect(p1[0]) + n);
        }
    }



    lemma exec_prog_append(p1: prog, p2: prog, s: stack)
        requires prog_stack_safe(p1 + p2, |s|)
        ensures (prog_stack_safe_append_elim(p1, p2, s);
                 exec_prog(p1 + p2, s) == exec_prog(p2, exec_prog(p1, s)))
    {
        if p1 != [] {
            assert (p1 + p2)[1..] == p1[1..] + p2;
            prog_stack_safe_append_elim(p1, p2, s);
        }
    }


    lemma compile_correct_stack(e: expr, s: stack)
        requires prog_stack_safe(compile(e), |s|)
        ensures exec_prog(compile(e), s) == [interp_expr(e)] + s
    {
        match e
            case Const(n) => {}
            case Plus(e1, e2) =>
                prog_stack_safe_append_elim(compile(e1) + compile(e2), [Add], s);
                prog_stack_safe_append_elim(compile(e1), compile(e2), s);
                calc {
                    exec_prog(compile(e), s);
                    == exec_prog(compile(e1) + compile(e2) + [Add], s);
                    == { exec_prog_append(compile(e1) + compile(e2), [Add], s); }
                       exec_prog([Add], exec_prog(compile(e1) + compile(e2), s));
                    == { exec_prog_append(compile(e1),  compile(e2), s); }
                       exec_prog([Add], exec_prog(compile(e2), exec_prog(compile(e1), s)));
                    == [interp_expr(e2) + interp_expr(e1)] + s;
                }
    }

    lemma compile_stack_safe(e: expr, n: nat)
        ensures prog_stack_safe(compile(e), n)
    {
        match e
            case Const(n) => {}
            case Plus(e1, e2) =>
                calc ==> {
                    true;
                    { prog_stack_safe_append_intro(compile(e1) + compile(e2), [Add], n); }
                    prog_stack_safe(compile(e1) + compile(e2) + [Add], n);
                    prog_stack_safe(compile(e), n);
                }
    
    }

/*    lemma compile_correct(e: expr)
        ensures exec_prog(compile(e), []) == [interp_expr(e)]
    {
        compile_correct_stack(e, []);
    }
*/
}
