// RUN: /rlimit:500000
// /noCheating:1

module AVL {
//    newtype balance = x: int | -1 <= x <= 1
    class Node {
        var left: Node
        var data: int
        var right: Node
//        var bal: balance

        ghost var repr: set<object>
        ghost var contents: set<int>

        constructor(x: int)
            ensures Valid() && contents == {x} && fresh(repr)
        {
            left := null;
            data := x;
            right := null;
            repr := {this};
            contents := {x};
            new;
        }

        predicate Valid()
            reads this, repr
        {
            && this in repr
            && null !in repr
            && (left != null ==>
                && left in repr
                && left.repr <= repr
                && this !in left.repr
                && (forall x | x in left.contents :: x < data)
                && left.Valid())
            && (right != null ==>
                && right in repr
                && right.repr <= repr
                && this !in right.repr
                && (forall x | x in right.contents :: x > data)
                && right.Valid())
            && GetRepr(left) !! GetRepr(right)
            && contents == GetContents(left) + GetContents(right) + {data}
        }

        static function GetRepr(n: Node): set<object>
            reads n
        {
            if n == null then {} else n.repr
        }

        static function GetContents(n: Node): set<int>
            reads n
        {
            if n == null then {} else n.contents
        }

        method {:rlimit 5000000} Insert(x: int)
            requires Valid()
            decreases repr
            modifies repr
            ensures Valid() && contents == old(contents) + {x} && fresh(repr - old(repr))
        {
            if x == data { return; }
            else if x < data {
                if left == null {
                    left := new Node(x);
                } else {
                    left.Insert(x);
                }
                repr := repr + left.repr;
            } else {
                if right == null {
                    right := new Node(x);
                } else {
                    right.Insert(x);
                }
                repr := repr + right.repr;
            }
            contents := contents + {x};
        }

        method Contains(x: int) returns (b: bool)
            requires Valid()
            decreases repr
            ensures b <==> x in contents
        {
            if x == data {
                return true;
            } else if x < data {
                if left == null {
                    return false;
                }
                b := left.Contains(x);
            } else {
                if right == null {
                    return false;
                }
                b := right.Contains(x);
            }
        }

        method {:rlimit 10000000} PopFront() returns (x: int, node: Node)
            requires Valid() && contents != {}
            modifies repr
            decreases repr
            ensures x in old(contents) && (forall y | y in old(contents) :: x <= y)
            ensures node != null ==> node.Valid() && fresh(node.repr - old(repr))
            ensures old(contents) - {x} == GetContents(node)
        {
            if left == null {
                x := data;
                node := right;
                return;
            }
            x, left := left.PopFront();
            repr := repr + GetRepr(left);
            contents := contents - {x};

            node := this;
        }

        method {:rlimit 10000000} Remove(x: int) returns (node: Node)
            requires Valid()
            modifies repr
            decreases repr
            ensures node != null ==> node.Valid() && fresh(node.repr - old(repr))
            ensures old(contents) - {x} == GetContents(node)
        {
            if x == data {
                if left == null {
                    return right;
                }
                if right == null {
                    return left;
                }
                data, right := right.PopFront();
                repr := repr + GetRepr(right);
            } else if x < data {
                if left != null {
                    left := left.Remove(x);
                    repr := repr + GetRepr(left);
                }
            } else {
                if right != null {
                    right := right.Remove(x);
                    repr := repr + GetRepr(right);
                }
            }
            contents := contents - {x};
            return this;
        }
    }

    class BST {
        var root: Node

        ghost var repr: set<object>
        ghost var contents: set<int>

        constructor BST()
        {
            root := null;
            repr := {};
            contents := {};
        }

        predicate Valid()
            reads this, repr
        {
            && null !in repr
            && this in repr
            && (root != null ==>
                && root in repr
                && this !in root.repr
                && root.repr <= repr
                && root.Valid()
                && contents == root.contents)
            && (root == null ==> contents == {})
        }

        method Contains(x: int) returns (b: bool)
            requires Valid()
            ensures b <==> x in contents
        {
            if root == null { return false; }
            b := root.Contains(x);
        }

        method Insert(x: int)
            requires Valid()
            modifies repr
            ensures Valid() && fresh(repr - old(repr)) && contents == old(contents) + {x}
        {
            if root == null {
                root := new Node(x);
            } else {
                root.Insert(x);
            }
            repr := repr + root.repr;
            contents := root.contents;
        }

        method Remove(x: int)
            requires Valid()
            modifies repr
            ensures Valid() && fresh(repr - old(repr)) && contents == old(contents) - {x}
        {
            if root == null { return; }

            root := root.Remove(x);
            repr := repr + Node.GetRepr(root);
            contents := Node.GetContents(root);
        }

    }
}

