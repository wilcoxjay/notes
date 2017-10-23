// RUN: /compile:0

type Pid = int
type FD = int
type RefCount = nat
type FileTableEntry = int

datatype File = File(in_use: bool, refcount: RefCount)

class State {
    var file_table: array<File>
    var proc_fd_tables: map<Pid, array<FileTableEntry>>

    ghost var repr: set<object>

    function References(f: int): set<(Pid, FD)>
        reads this, repr
        requires ReprValid()
        requires forall proc | proc in proc_fd_tables :: proc_fd_tables[proc] != null
    {
        set proc, fd |
            && proc in proc_fd_tables
            && 0 <= fd < proc_fd_tables[proc].Length
            && proc_fd_tables[proc][fd] == f
            :: (proc, fd)
    }

    predicate ReprValid()
        reads this, repr
    {
        && this in repr
        && null !in repr
        && file_table in repr
        && (forall proc | proc in proc_fd_tables :: proc_fd_tables[proc] in repr)
    }

    predicate Valid()
        reads this, repr
    {
        && ReprValid()
        && (forall proc, fd | proc in proc_fd_tables && 0 <= fd < proc_fd_tables[proc].Length ::
            var f := proc_fd_tables[proc][fd];
            f == -1 || (0 <= f < file_table.Length && file_table[f].in_use))
        && (forall p1, p2 | p1 in proc_fd_tables && p2 in proc_fd_tables && p1 != p2 ::
            proc_fd_tables[p1] != proc_fd_tables[p2])
        && (forall f | 0 <= f < file_table.Length ::
            && file_table[f].refcount == |References(f)|
            && (file_table[f].in_use <==> file_table[f].refcount > 0))
    }
}

method Dup(s: State, proc: Pid, oldfd: FD) returns (ok: bool, newfd: FD)
    requires s != null && s.Valid() && proc in s.proc_fd_tables
    modifies s.repr
    ensures s.Valid()
    ensures s.proc_fd_tables == old(s.proc_fd_tables)
    ensures forall proc' | proc' != proc && proc' in s.proc_fd_tables ::
        s.proc_fd_tables[proc'][..] == old(s.proc_fd_tables[proc'][..])

    ensures ok ==>
        && 0 <= oldfd < s.proc_fd_tables[proc].Length
        && 0 <= newfd < s.proc_fd_tables[proc].Length
        && s.proc_fd_tables[proc][oldfd] == s.proc_fd_tables[proc][newfd]
        && (forall fd | 0 <= fd < newfd :: s.proc_fd_tables[proc][fd] != -1)
        && (forall fd | 0 <= fd < s.proc_fd_tables[proc].Length && fd != newfd ::
            s.proc_fd_tables[proc][fd] == old(s.proc_fd_tables[proc][fd]))
{
    var fd_table := s.proc_fd_tables[proc];
    if oldfd < 0 || oldfd >= fd_table.Length || fd_table[oldfd] == -1 { ok := false; return; }

    newfd := 0;
    ok := false;
    while newfd < fd_table.Length
        modifies {}
        invariant 0 <= newfd <= fd_table.Length
        invariant (forall fd | 0 <= fd < newfd :: s.proc_fd_tables[proc][fd] != -1)
    {
        if fd_table[newfd] == -1 { ok := true; break; }
        newfd := newfd + 1;
    }
    if !ok { return; }

    assert 0 <= newfd < fd_table.Length && fd_table[newfd] == -1;

    assert oldfd != newfd;
    var f := fd_table[oldfd];
    fd_table[newfd] := f;
    s.file_table[f] := s.file_table[f].(refcount := s.file_table[f].refcount + 1);

    forall f' | 0 <= f' < s.file_table.Length && s.file_table[f'].in_use
        ensures s.file_table[f'].refcount == |s.References(f')|
    {
        if f == f' {
            assert s.References(f) == old(s.References(f)) + {(proc, newfd)};
        } else {
            assert s.References(f') == old(s.References(f'));
        }
    }

    return;
}

method DupFinite(s: State, proc: Pid, oldfd: FD, newfd: FD) returns (ok: bool)
    requires s != null && s.Valid() && proc in s.proc_fd_tables
    modifies s.repr
    ensures s.Valid()
    ensures s.proc_fd_tables == old(s.proc_fd_tables)
    ensures forall proc' | proc' != proc && proc' in s.proc_fd_tables ::
        s.proc_fd_tables[proc'][..] == old(s.proc_fd_tables[proc'][..])

    ensures ok ==>
        && 0 <= oldfd < s.proc_fd_tables[proc].Length
        && 0 <= newfd < s.proc_fd_tables[proc].Length
        && s.proc_fd_tables[proc][oldfd] == s.proc_fd_tables[proc][newfd]
        && (forall fd | 0 <= fd < s.proc_fd_tables[proc].Length && fd != newfd ::
            s.proc_fd_tables[proc][fd] == old(s.proc_fd_tables[proc][fd]))
{
    var fd_table := s.proc_fd_tables[proc];
    if oldfd < 0 || oldfd >= fd_table.Length || fd_table[oldfd] == -1 { return false; }
    if newfd < 0 || newfd >= fd_table.Length || fd_table[newfd] != -1 { return false; }

    assert oldfd != newfd;
    var f := fd_table[oldfd];
    fd_table[newfd] := f;
    s.file_table[f] := s.file_table[f].(refcount := s.file_table[f].refcount + 1);

    forall f' | 0 <= f' < s.file_table.Length && s.file_table[f'].in_use
        ensures s.file_table[f'].refcount == |s.References(f')|
    {
        if f == f' {
            assert s.References(f) == old(s.References(f)) + {(proc, newfd)};
        } else {
            assert s.References(f') == old(s.References(f'));
        }
    }

    return true;
}

lemma CardinalitySubset<T>(A: set<T>, B: set<T>)
    requires A <= B
    ensures |A| <= |B|
{
    if A == B {
        return;
    } else {
        assert A < B;
        var x :| x in B && x !in A;
        CardinalitySubset(A, B - {x});
    }
}

lemma CardinalityOne<T>(S: set<T>, x: T)
    requires |S| == 1 && x in S
    ensures S == {x}
{
    forall y | y in S
        ensures y == x
    {
        if y != x {
            CardinalitySubset({x, y}, S);
        }
    }
}

lemma ValidReferences(s: State)
    requires s != null && s.Valid()
{}

method Close(s: State, proc: Pid, fd: FD) returns (ok: bool)
    requires s != null && s.Valid() && proc in s.proc_fd_tables
    modifies s.repr
    ensures s.Valid()
    ensures s.proc_fd_tables == old(s.proc_fd_tables)
    ensures forall proc' | proc' != proc && proc' in s.proc_fd_tables ::
        s.proc_fd_tables[proc'][..] == old(s.proc_fd_tables[proc'][..])
{
    var fd_table := s.proc_fd_tables[proc];
    if fd < 0 || fd >= fd_table.Length || fd_table[fd] == -1 { return false; }

    var file := fd_table[fd];

    if s.file_table[file].refcount == 1 {
        assert forall proc', fd' |
            && proc' in s.proc_fd_tables
            && 0 <= fd' < s.proc_fd_tables[proc'].Length
            :: (proc', fd') in s.References(file) || s.proc_fd_tables[proc'][fd'] != file;
    
        assert s.References(file) == {(proc, fd)} by {
            CardinalityOne(s.References(file), (proc, fd));
        }
    }

    fd_table[fd] := -1;

    s.file_table[file] := s.file_table[file].(refcount := s.file_table[file].refcount - 1);

    if s.file_table[file].refcount == 0 {
        s.file_table[file] := s.file_table[file].(in_use := false);
    }

    forall f | 0 <= f < s.file_table.Length
        ensures s.file_table[f].refcount == |s.References(f)|
        ensures s.file_table[f].in_use <==> s.file_table[f].refcount > 0
    {
        if file == f {
            assert s.References(file) == old(s.References(file)) - {(proc, fd)};
        } else {
            assert s.References(f) == old(s.References(f));
        }
    }
}
