// Machine ints for hashes.
type uint32 = x: int | 0 <= x <= 0xFFFFFFFF

// Assume there's some type for the data in the DAG.
type Data

// Assume there are some functions to manipulate hashes.
function HashData(d: Data): uint32
function HashCombine(n1: uint32, n2: uint32): uint32
function HashSequence(s: seq<uint32>): uint32

// Each node has some data, some children, and a hash summary.
// The directedness of the structure is captured by the inductiveness
// of this datatype: no node can have its ancestors as children.
datatype MerkleNode = MerkleNode(data: Data, children: seq<MerkleNode>, hash: uint32)

// Helper function to get a list of hashes from a list of nodes.
function Hashes(l: seq<MerkleNode>): seq<uint32>
{
    if l == [] then
        [] 
    else 
        [l[0].hash] + Hashes(l[1..])
}

// What it means for a MerkleNode to be well formed: its children are
// well formed, and its hash correctly summarizes the children and data.
predicate MerkleNodeValid(m: MerkleNode)
{
    && (forall child | child in m.children :: MerkleNodeValid(child))
    && m.hash == HashCombine(HashData(m.data), HashSequence(Hashes(m.children)))
}
