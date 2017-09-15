// RUN: /compile:0  /rlimit:1000000

module Prelude {
    type Data
    type Time = real
    type uint32 = x: int | 0 <= x < 0xFFFFFFFF
    type Hash = uint32
    
    function HashData(d: Data): Hash
    function HashList(l: seq<Hash>): Hash

    function MapRemove<A(==),B>(m: map<A, B>, a: A): map<A, B>
    {
        map x | x in m && x != a :: m[x]
    }
}

module Dedup {
    import opened Prelude

    datatype Dedup = 
        | DChunk(data: Data, hash: Hash, KU: Time)
        | DNode(children: seq<Hash>, hash: Hash, KU: Time)
    
    datatype State = State(dedups: map<Hash, Dedup>, refs: set<(Hash, Hash)>, now: Time)
    
    function DedupUpdateKU(d: Dedup, ku: Time): Dedup 
    {
        match d 
            case DChunk(data, hash, _) => DChunk(data, hash, ku)
            case DNode(children, hash, _) => DNode(children, hash, ku)
    }

    predicate DeleteDedup(s: State, s': State)
    {
        && s'.refs == s.refs
        && s'.now == s.now
        && exists hash {:trigger MapRemove(s.dedups, hash)} | hash in s.dedups :: 
            var d := s.dedups[hash];
            && d.KU < s.now
            && (forall h | h in s.dedups && s.dedups[h].DNode? :: hash !in s.dedups[h].children)
            && s'.dedups == MapRemove(s.dedups, hash)
    }
    
    predicate ClockTick(s: State, s': State)
    {
        && s'.dedups == s.dedups
        && s'.refs == s.refs
        && s'.now >= s.now
    }
    
    predicate ExtendKU(s: State, s': State, h: Hash, ku: Time)
    {
        && s'.refs == s.refs
        && s'.now == s.now
        && h in s.dedups
        && var d := s.dedups[h];
        && ku >= d.KU
        && (d.DNode? ==> forall h' | h' in d.children && h' in s.dedups :: s.dedups[h'].KU >= ku)
        && s'.dedups == s.dedups[h := DedupUpdateKU(d, ku)]
    }

    predicate Inv(s: State)
    {
        && (forall h, h' | h in s.dedups :: var d := s.dedups[h];
            && d.DNode? 
            && h' in d.children 
            ==> 
            && h' in s.dedups
            && var d' := s.dedups[h'];
            && d'.KU >= d.KU)
    }

    predicate Next(s: State, s': State)
    {
        || DeleteDedup(s, s')
        || ClockTick(s, s')
        || (exists h: Hash, ku :: ExtendKU(s, s', h, ku))
    }

    lemma InvInductive(s: State, s': State)
        requires Inv(s) && Next(s, s')
        ensures Inv(s')
    { }
}


module DedupTree {
    import opened Prelude
    import Dedup

    datatype DedupTree = 
        | DTChunk(data: Data, hash: Hash, KU: Time)
        | DTNode(children: seq<DedupTree>, hash: Hash, KU: Time)
    
    predicate InTree(d: Dedup.Dedup, t: DedupTree)
    {
        match t
            case DTChunk(data, hash, KU) => d == Dedup.DChunk(data, hash, KU)
            case DTNode(children, hash, KU) => 
                || d == Dedup.DNode(Hashes(children), hash, KU)
                || exists c | c in children :: InTree(d, c)
    }
    
    function Hashes(l: seq<DedupTree>): seq<Hash>
    {
        if l == [] then
            []
        else 
            [l[0].hash] + Hashes(l[1..])
    }
    
    predicate DedupTreeValid(m: DedupTree)
    {
        match m 
            case DTChunk(d,h,_) => h == HashData(d)
            case DTNode(children, h, ku) => 
                && (forall child | child in children :: DedupTreeValid(child) && ku <= child.KU)
                && h == HashList(Hashes(children))
    }
    
    predicate DedupsMatchTrees(dedups: map<Hash, Dedup.Dedup>, trees: set<DedupTree>)
    {
        && (forall h | h in dedups :: exists t | t in trees :: InTree(dedups[h], t))
        && (forall t, d | t in trees && InTree(d, t) :: d.hash in dedups && dedups[d.hash] == d)
    }
}
