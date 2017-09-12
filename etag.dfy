newtype Id = int
newtype Root = int
newtype Time = int
newtype ETag = i : int | i >= 0
datatype Ref = BackPointer(Id) | Root(int)
datatype GcPhase = Idle | Mark | Sweep
datatype CompareSwap<T> = Success(T) | Retry
datatype Maybe<T> = Some(T) | None
datatype PutResult = Stored | SwapFailure | ChildrenNeedKeepUntil


class DedupContent
{
    var id : Id;
    var children: set<Id>;
}

class EtagObject<T(0)>
{
    var etag: ETag;    
    var obj: T;       
}

class DedupBlob
{
    var content: DedupContent;
    var keepUntil: Time;

    function method Valid() : bool 
        reads this
    {
        content != null
    }
}

class DedupRefs
{
    var cachedKeepUntil: Time;
    var refs: set<Ref>;

    function method Valid() : bool {
        true
    }
}

class AzureBlob
{
    var objs: map<Id,EtagObject<DedupBlob>>;

    predicate Valid()
        reads *
    {
        (forall i :: i in objs ==> objs[i] != null && objs[i].obj != null && objs[i].obj.Valid())
    }

    function method tryGet(id : Id) : (b : Maybe<EtagObject<DedupBlob>>)
        requires Valid()
        reads *
//        ensures Valid()
//        ensures id in objs ==> b == Some(objs[id])
//        ensures !(id in objs) ==> b == None
    {
        if id in objs then Some(objs[id]) else None
    }

    function method get(id : Id) : (b : EtagObject<DedupBlob>)
        reads *
        requires id in objs
        requires Valid()
//        ensures Valid()
//        ensures b != null
//        ensures b == objs[id]
    {
        objs[id]
    }

    method tryInsert(id: Id, b: DedupBlob) returns (r : bool)
        requires Valid()
        requires b != null && b.Valid()
        modifies this
        ensures Valid()
        ensures id in objs
        ensures r ==> objs[id].obj != null && objs[id].obj == b && objs[id].etag == 0
        ensures !r ==> id in old(objs)
        ensures forall i :: i in old(objs) ==> i in objs && objs[i] == old(objs[i])
        ensures forall i :: i in objs ==>  i == id || (i in old(objs) && objs[i] == old(objs[i]))
    {
        if (id in objs) {
            r := false;
        } else {
            var obj := new EtagObject<DedupBlob>;
            obj.etag := 0;
            obj.obj := b;
            objs := objs[id := obj];
            r := true;
        }
    }

    method tryReplace(id: Id, b: DedupBlob, e: ETag) returns (r : bool)
        requires Valid()
        requires b != null && b.Valid()        
        modifies this
        ensures Valid()
        ensures r ==> id in objs && objs[id].obj != null && objs[id].obj == b && objs[id].etag == e + 1
        ensures !r ==> !(id in old(objs)) || (id in old(objs) && old(objs[id].etag) != e)
        ensures forall i :: i in old(objs) ==> i in objs && (objs[i] == old(objs[i]) || (r && i == id))
        ensures forall i :: i in objs ==>  (r && i == id) || (i in old(objs) && objs[i] == old(objs[i]))
    {
        if (id in objs && objs[id].etag == e) {
            var obj := new EtagObject<DedupBlob>;
            obj.etag := objs[id].etag + 1;
            obj.obj := b;
            objs := objs[id := obj];
            r := true;
        } else {
            r := false;
        }
    }
}

class AzureTable
{
    var objs: map<Id,EtagObject<DedupRefs>>;

    predicate Valid()
        reads *
    {
        (forall i :: i in objs ==> objs[i] != null && objs[i].obj != null && objs[i].obj.Valid())
    }

    function method tryGet(id : Id) : (b : Maybe<EtagObject<DedupRefs>>)
        requires Valid()
        reads *
  //      ensures Valid()
//        ensures id in objs ==> b == Some(objs[id])
//        ensures !(id in objs) ==> b == None
    {
        if id in objs then Some(objs[id]) else None
    }

    function method get(id : Id) : (b : EtagObject<DedupRefs>)
        reads *
        requires id in objs
        requires Valid()
//        ensures Valid()
//        ensures b != null
//        ensures b == objs[id]
    {
        objs[id]
    }

    method tryInsert(id: Id, b: DedupRefs) returns (r : bool)
        requires Valid()
        requires b != null && b.Valid()
        modifies this
        ensures Valid()
        ensures id in objs
        ensures r ==> objs[id].obj != null && objs[id].obj == b && objs[id].etag == 0
        ensures !r ==> id in old(objs)
        ensures forall i :: i in old(objs) ==> i in objs && objs[i] == old(objs[i])
        ensures forall i :: i in objs ==>  i == id || (i in old(objs) && objs[i] == old(objs[i]))
    {
        if (id in objs) {
            r := false;
        } else {
            var obj := new EtagObject<DedupRefs>;
            obj.etag := 0;
            obj.obj := b;
            objs := objs[id := obj];
            r := true;
        }
    }

    method tryReplace(id: Id, b: DedupRefs, e: ETag) returns (r : bool)
        requires Valid()
        requires b != null && b.Valid()        
        modifies this
        ensures Valid()
        ensures r ==> id in objs && objs[id].obj != null && objs[id].obj == b && objs[id].etag == e + 1
        ensures !r ==> !(id in old(objs)) || (id in old(objs) && old(objs[id].etag) != e)
        ensures forall i :: i in old(objs) ==> i in objs && (objs[i] == old(objs[i]) || (r && i == id))
        ensures forall i :: i in objs ==>  (r && i == id) || (i in old(objs) && objs[i] == old(objs[i]))
    {
        if (id in objs && objs[id].etag == e) {
            var obj := new EtagObject<DedupRefs>;
            obj.etag := objs[id].etag + 1;
            obj.obj := b;
            objs := objs[id := obj];
            r := true;
        } else {
            r := false;
        }
    }
}


class DedupDomain
{
    var azureBlob: AzureBlob;
    var azureTable: AzureTable;

    var gc: GcPhase;

    predicate Valid() 
        reads *
    {
        // Sanity checks
        (azureBlob != null) && (azureBlob.Valid()) &&
        (azureTable != null) && (azureTable.Valid()) &&

        // There is always an index if there is a blob
        (forall i :: i in azureBlob.objs ==> i in azureTable.objs) && 

        // Cached keep until is bounded one-way
        (forall i :: i in azureBlob.objs ==> azureBlob.get(i).obj.keepUntil >= azureTable.get(i).obj.cachedKeepUntil) &&

        // Children outlive parents
        (forall i :: i in azureBlob.objs ==> (forall j :: j in azureBlob.get(i).obj.content.children ==>
            j in azureBlob.objs && azureBlob.get(j).obj.keepUntil >= azureBlob.get(i).obj.keepUntil))  
    }
    
     method put(d: DedupContent, k: Time, now: Time) returns (r : PutResult)
        requires Valid()
        requires d != null
        requires k > now
        modifies this, azureTable, azureBlob
        ensures Valid()
        ensures d != null
        ensures match r
            case SwapFailure => true
            case Stored => (match azureBlob.tryGet(d.id)
                case None => true
                case Some(b) => b.obj.keepUntil >= k)
            case ChildrenNeedKeepUntil => true // TODO: ensure this succeeds when it should

    {
        match azureBlob.tryGet(d.id) {
            case None => {
                if (forall i :: i in d.children ==> match azureBlob.tryGet(i) 
                        case None => false 
                        case Some(b) => b.obj.keepUntil >= k) {
                    // Insert in index
                    match azureTable.tryGet(d.id) {
                        case None => {
                            var ref := new DedupRefs;
                            ref.cachedKeepUntil := k;
                            assert Valid();                            
                            var result := azureTable.tryInsert(d.id, ref);
                            assert Valid();
                            if (!result) {
                                r := SwapFailure;
                                return;
                            }
                        }
                        case Some(existingRef) => {
                            // ugh this seems wrong
                            if (existingRef.obj.cachedKeepUntil > k) {
                                var ref := new DedupRefs;
                                ref.cachedKeepUntil := k;
                                ref.refs := existingRef.obj.refs;
                                assert Valid();                    
                                var result := azureTable.tryReplace(d.id, ref, existingRef.etag);
                                assert Valid();
                                if (!result) {
                                    r := SwapFailure;
                                    return;
                                }
                            }
                        }
                    }
                    
                    var b := new DedupBlob;
                    b.keepUntil := k;
                    b.content := d;
                    assert Valid();
                    var insertResult := azureBlob.tryInsert(d.id, b);
                    assert Valid();
                    if insertResult {
                        r := Stored;
                    } else {
                        r := SwapFailure;
                    }
                } else {
                    r := ChildrenNeedKeepUntil;
                }
            }
            case Some(existing) => {
                // TODO: Embed CAS in azure blob layer
                assume d.children == existing.obj.content.children;
                if (existing.obj.keepUntil < k) {
                    if (forall i :: i in d.children ==> match azureBlob.tryGet(i) 
                                                            case None => false
                                                            case Some(b) => b.obj.keepUntil >= k) {
                        var updated : DedupBlob := new DedupBlob;
                        updated.content := existing.obj.content;
                        updated.keepUntil := k;
                        assert Valid();     
                        var result := azureBlob.tryReplace(d.id, updated, existing.etag);
                        assert Valid();
                        if result {
                            r := Stored;
                        } else {
                            r := SwapFailure;
                        }
                    } else {
                        r := ChildrenNeedKeepUntil;
                    }
                } else {
                    r := Stored;
                }
            }
        }
    }
}
