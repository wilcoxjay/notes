// RUN: /compile:0

type Pid = int
type FD = int
type RefCount = int
type FileTableEntry = int

class State {
    var file_table: array<RefCount>
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
        && (forall proc | proc in proc_fd_tables ::
            && (forall fd | 0 <= fd < proc_fd_tables[proc].Length ::
                var f := proc_fd_tables[proc][fd];
                f == -1 || 0 <= f < file_table.Length))
        && (forall p1, p2 | p1 in proc_fd_tables && p2 in proc_fd_tables && p1 != p2 ::
            proc_fd_tables[p1] != proc_fd_tables[p2])
        && (forall proc | proc in proc_fd_tables :: proc_fd_tables[proc] != file_table)
        && (forall f | 0 <= f < file_table.Length :: file_table[f] == |References(f)|)
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
        && (forall fd | 0 <= fd < s.proc_fd_tables[proc].Length && fd != newfd ::
            s.proc_fd_tables[proc][fd] == old(s.proc_fd_tables[proc][fd]))
{
    var fd_table := s.proc_fd_tables[proc];
    if oldfd < 0 || oldfd >= fd_table.Length || fd_table[oldfd] == -1 { ok := false; return; }

    newfd := 0;
    ok := false;
    while newfd < fd_table.Length
        modifies {}
    {
        if fd_table[newfd] == -1 { ok := true; break; }
        newfd := newfd + 1;
    }
    if !ok { return; }

    assert 0 <= newfd < fd_table.Length && fd_table[newfd] == -1;

    assert oldfd != newfd;
    var f := fd_table[oldfd];
    fd_table[newfd] := f;
    s.file_table[f] := s.file_table[f] + 1;

    forall f' | 0 <= f' < s.file_table.Length
        ensures s.file_table[f'] == |s.References(f')|
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
    s.file_table[f] := s.file_table[f] + 1;

    forall f' | 0 <= f' < s.file_table.Length
        ensures s.file_table[f'] == |s.References(f')|
    {
        if f == f' {
            assert s.References(f) == old(s.References(f)) + {(proc, newfd)};
        } else {
            assert s.References(f') == old(s.References(f'));
        }
    }

    return true;
}
