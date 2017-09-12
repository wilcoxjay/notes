type NodeId(==)

datatype Payload = Ping | Pong

datatype Message = Message(payload: Payload, from: NodeId, to: NodeId)

class WorldState {
    var network: set<Message>
    var node_state
}

method Main()
    decreases *
{
    while true
        decreases *
    {
    }
}
