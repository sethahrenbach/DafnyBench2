
module Base {
    datatype INodePort = inodeport(node_id: nat, port_id: nat)
    datatype ONodePort = onodeport(node_id: nat, port_id: nat)

    datatype Node = Xor | And | Ident

    function n_iports(node: Node): nat {
        match node {
            case Xor => 2
            case And => 2
            case Ident => 1
        }
    }

    function n_oports(node: Node): nat {
        match node {
            case Xor => 1
            case And => 1
            case Ident => 1
        }
    }

    datatype Circuit = Circ(
        nodes: seq<Node>,
        backconns: map<INodePort, ONodePort>
    )

    predicate WellformedBackConns(c: Circuit) {
        forall inp :: inp in c.backconns ==>
            WellformedINP(c, inp) &&
            WellformedONP(c, c.backconns[inp])
    }

    predicate WellformedINP(c: Circuit, inp: INodePort) {
        (0 <= inp.node_id < |c.nodes|) && (inp.port_id < n_iports(c.nodes[inp.node_id]))
    }

    predicate WellformedONP(c: Circuit, onp: ONodePort) {
        (0 <= onp.node_id < |c.nodes|) && (onp.port_id < n_oports(c.nodes[onp.node_id]))
    }

    function AllINPs(c: Circuit): set<INodePort>
        ensures forall inp :: inp in AllINPs(c) ==> WellformedINP(c, inp)
    {
        set node_id: nat, port_id: nat |
            0 <= node_id < |c.nodes| && port_id < n_iports(c.nodes[node_id]) ::
            inodeport(node_id, port_id)
    }

    function AllONPs(c: Circuit): set<ONodePort>
        ensures forall onp :: onp in AllONPs(c) ==> WellformedONP(c, onp)
    {
        set node_id: nat, port_id: nat |
            0 <= node_id < |c.nodes| && port_id < n_oports(c.nodes[node_id]) ::
            onodeport(node_id, port_id)
    }

    ghost predicate Wellformed(c: Circuit) {
        WellformedBackConns(c)
    }
}

module Utils {
    function UpdateMap<T(!new), U>(A: map<T, U>, f: T->T, g: U->U): (result: map<T, U>)
        requires forall x: T, y: T :: x != y ==> f(x) != f(y)
        ensures forall x :: x in A <==> f(x) in result;
        ensures forall x :: x in A ==> g(A[x]) == result[f(x)];
    {
        map x | x in A :: f(x) := g(A[x])
    }

    function CombineMaps<T(!new), U>(a: map<T, U>, b: map<T, U>): map<T, U>
        requires forall x :: x in a ==> x !in b
        requires forall x :: x in b ==> x !in a
        ensures
            var result := CombineMaps(a, b);
            (forall x :: x in a ==> a[x] == result[x]) &&
            (forall x :: x in b ==> b[x] == result[x]) &&
            (forall x :: x in result ==> (x in a) || (x in b))
    {
        map x | x in (a.Keys + b.Keys) :: if x in a then a[x] else b[x]
    }

    function sub(a: nat, b: nat): nat
        requires b <= a
    {
        a - b
    }
}

module BackwardConnections {
    import opened Base
    import opened Utils

    function CombineBackconns(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>): (result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
    {
        var f:= (inp: INodePort) => inodeport(inp.node_id + offset, inp.port_id);
        var g := (onp: ONodePort) => onodeport(onp.node_id + offset, onp.port_id);
        var backconns2 := UpdateMap(bc2, f, g);
        CombineMaps(bc1, backconns2)
    }

    lemma CombineBackconnsHelper(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        ensures
            forall inp :: inp in bc1 ==> (
                inp in result &&
                result[inp] == bc1[inp])
        ensures
            forall inp :: inp in bc2 ==> (
                inodeport(inp.node_id+offset, inp.port_id) in result &&
                result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id))
    {
        var f:= (inp: INodePort) => inodeport(inp.node_id + offset, inp.port_id);
        var g := (onp: ONodePort) => onodeport(onp.node_id + offset, onp.port_id);
        var backconns2 := UpdateMap(bc2, f, g);
    }
}
