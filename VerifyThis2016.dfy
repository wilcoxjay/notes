// RUN: /compile:0 /nologo /printTooltips

module Challenge2 {
    datatype BinaryTree = Leaf | Node(left: BinaryTree, mark: bool, right: BinaryTree)

    function MarkBinaryTree(b: BinaryTree): BinaryTree
    {
        match b 
            case Leaf => Leaf
            case Node(l, _, r) => Node(MarkBinaryTree(l), true, MarkBinaryTree(r))
    }

    class Tree {
        var left: Tree;
        var right: Tree;
        var parent: Tree;
        var mark: bool;

        ghost var repr: set<object>

        predicate Tree(contents: BinaryTree)
            reads this, repr
        {
            && this in repr
            && null !in repr
            && (left == null <==> right == null)
            && (left == null ==> contents.Leaf?)
            && (left != null ==> 
                && left in repr 
                && left.repr <= repr
                && this !in left.repr
                && contents.Node?
                && left.Tree(contents.left)
                && left.parent == this

                && right in repr 
                && right.repr <= repr
                && this !in right.repr
                && right.Tree(contents.right)
                && right.parent == this

                && mark == contents.mark

                && left.repr !! right.repr)
        }

        predicate TreeRoot(contents: BinaryTree)
            reads this, repr
        {
            && Tree(contents)
            && parent == null
        }
    }

    predicate Stack(root: Tree, parent: Tree, current: Tree, contents: BinaryTree)
        requires current != null
        reads current, current.repr, parent
    {
        if parent == null then
            && current == root
            && current.Tree(contents)
        else 
            && parent.parent == current
            && false
    }


    predicate Inv(root: Tree, current: Tree, firstTime: bool)
        reads current, if current != null then current.repr else {}
    {
        if firstTime then
            && current != null
            && exists contents :: current.Tree(contents)
        else 
            false
    }

    method markTree(root: Tree, ghost contents: BinaryTree)
        requires root != null
        requires root.TreeRoot(contents)
        modifies root.repr
    {
/*        var x: Tree := root;
        var y: Tree;
        while true 
        {
            x.mark := true;
            if x.left == null && x.right == null {
                y := x.parent;
            } else {
                assert x.left != null && x.right != null;
                y := x.left;
                x.left := x.right;
                x.right := x.parent;
                x.parent := y;
            }
            x := y;
            if x == null
            {
                break;
            }
        }
*/
    }

}
/*
module Challenge3 {
    datatype Tree<A> = Empty | Node(data: A, left: Tree<A>, right: Tree<A>)

    predicate method InTree<A(==)>(x: A, t: Tree<A>)
    {
        && t.Node?
        && (|| t.data == x
            || InTree(x, t.left)
            || InTree(x, t.right))
    }

    function method TreeElements<A>(t: Tree<A>): set<A>
    {
        match t 
            case Empty => {}
            case Node(x, l, r) => {x} + TreeElements(l) + TreeElements(r)
    }

    lemma lemma_TreeElements_InTree<A(==)>(x: A, t: Tree<A>)
        ensures InTree(x, t) <==> x in TreeElements(t)
    {}

    class Node {
        var left: Node
        var right: Node
        var parent: Node

        var sense: bool

        var repr: set<Node>
        var contents: Tree<Node>

        predicate Valid()
            reads this, repr
        {
            && this in repr
            && null !in repr
            && contents.Node?
            && contents.data == this
            && (left != null ==> 
                && left in repr
                && left.repr <= repr
                && this !in left.repr
                && left.Valid()
                && left.parent == this
                && contents.left == left.contents)
            && (right != null ==> 
                && right in repr
                && right.repr <= repr
                && this !in right.repr
                && right.Valid()
                && right.parent == this
                && contents.right == right.contents)
            && (left != null && right != null ==> 
                left.repr !! right.repr)
        }
        
        predicate ValidRoot()
            reads this, repr
        {
            && Valid()
            && parent == null
        }
    }

    datatype PC = PC0 | PC1 | PC2 | PC3 | PC4 | PC5 | PC6

    method Main(root: Node)
        decreases *
        requires root != null && root.ValidRoot()
        modifies root.repr
    {
        var state := map t | t in TreeElements(root.contents) :: PC0;

        while true
            decreases *
            invariant state.Keys == TreeElements(root.contents)
        {
            var t :| t in TreeElements(root.contents);

            //match state[t]
        }
    }
    
}
*/


/*

/*@

inductive tree = empty(Tree node) | nonempty(Tree node, tree left, tree right);

fixpoint int node_count(tree tree) {
    switch (tree) {
        case empty(node): return 1;
        case nonempty(node, left, right): return 1 + node_count(left) + node_count(right);
    }
}

lemma_auto void node_count_positive(tree tree)
    requires true;
    ensures node_count(tree) >= 1;
{
    switch (tree) {
        case empty(node):
        case nonempty(node, left, right):
            node_count_positive(left);
            node_count_positive(right);
    }
}

predicate tree(Tree node, boolean marked; Tree parent, tree shape) =
    node.left |-> ?left &*&
    node.right |-> ?right &*&
    node.mark |-> ?mark &*& (marked ? mark == true : true) &*&
    node.parent |-> parent &*&
    left == null ?
        right == null &*&
        shape == empty(node)
    :
        right != null &*&
        tree(left, marked, node, ?leftShape) &*&
        tree(right, marked, node, ?rightShape) &*&
        shape == nonempty(node, leftShape, rightShape);

predicate stack(Tree parent, Tree current, tree currentNodeShape, Tree root, tree rootShape, int stepsLeft) =
    current != null &*&
    parent == null ?
        root == current &*& rootShape == currentNodeShape &*& stepsLeft == 0
    :
        parent.left |-> ?left &*&
        parent.right |-> ?right &*&
        parent.mark |-> true &*&
        parent.parent |-> current &*&
        exists<boolean>(?currentIsLeftChild) &*&
        currentIsLeftChild ?
            tree(left, false, parent, ?rightShape) &*& left != null &*&
            stack(right, parent, nonempty(parent, currentNodeShape, rightShape), root, rootShape, ?stepsLeft1) &*& stepsLeft1 >= 0 &*&
            stepsLeft == node_count(rightShape) * 2 + 1 + stepsLeft1
        :
            tree(right, true, parent, ?leftShape) &*& right != null &*&
            stack(left, parent, nonempty(parent, leftShape, currentNodeShape), root, rootShape, ?stepsLeft1) &*& stepsLeft1 >= 0 &*&
            stepsLeft == 1 + stepsLeft1;

lemma void tree_nonnull(Tree t)
    requires tree(t, ?marked, ?parent, ?shape);
    ensures tree(t, marked, parent, shape) &*& t != null;
{
    open tree(t, marked, parent, shape);
    close tree(t, marked, parent, shape);
}

predicate inv(boolean xIsNew, Tree x, Tree root, tree rootShape, int stepsLeft) =
        xIsNew ?
            tree(x, false, ?parent, ?xShape) &*& stack(parent, x, xShape, root, rootShape, ?stepsLeft1) &*&
            stepsLeft1 >= 0 &*& stepsLeft == node_count(xShape) * 2 - 1 + stepsLeft1
        :
            stack(x, ?child, ?childShape, root, rootShape, stepsLeft) &*& stepsLeft >= 0 &*&
            tree(child, true, x, childShape);
    

@*/

class Tree {
	Tree left, right, parent;
	boolean mark;
	
	static void markTree(Tree root)
	    //@ requires tree(root, false, null, ?rootShape);
	    //@ ensures tree(root, true, null, rootShape);
	{
		Tree x = root;
		//@ tree_nonnull(x);
		//@ close stack(null, root, rootShape, root, rootShape, 0);
		//@ close inv(true, x, root, rootShape, _);
		do
		    //@ invariant inv(?xIsNew, x, root, rootShape, ?stepsLeft) &*& x != null;
		    //@ decreases stepsLeft;
		{
			//@ open inv(_, _, _, _, _);
			/*@
			if (xIsNew) {
			} else {
				open stack(x, ?child, ?childShape, root, rootShape, _);
			}
			@*/
	  		x.mark = true;
	  		Tree y;
	  		if (x.left == null && x.right == null) {
	    		  	y = x.parent;
	    		  	//@ close inv(false, y, root, rootShape, _);
	  		} else {
	    			y = x.left;
	    			x.left = x.right;
	    			x.right = x.parent;
	    			x.parent = y;
	    			/*@
	    			if (xIsNew) {
	    			    assert tree(y, false, x, ?leftShape);
	    			    close exists(true);
	    			    close stack(x, y, leftShape, root, rootShape, _);
	    			    close inv(true, y, root, rootShape, _);
	    			} else {
	    			    open exists(?currentIsLeftChild);
	    			    if (currentIsLeftChild) {
	    			        close exists(false);
	    			        assert tree(y, false, x, ?rightShape);
	    			        tree_nonnull(x.right);
	    			        close stack(x, y, rightShape, root, rootShape, _);
	    			        close inv(true, y, root, rootShape, _);
	    			    } else {
	    			        close inv(false, y, root, rootShape, _);
	    			    }
	    			}
	    			@*/
	  		}
		 	x = y;
		} while (x != null);
		//@ open inv(_, _, _, _, _);
		//@ open stack(null, _, _, _, _, _);
	}
}

*/
