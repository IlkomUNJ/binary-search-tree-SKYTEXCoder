mod structure;
mod tool;

use std::rc::Rc;

use crate::structure::bst::{BstNode, BstNodeLink};
use crate::structure::tree::{Node, NodeLink};
use crate::tool::{
    generate_dotfile, generate_dotfile_bst, generate_dotfile_bst_better, print_graph,
};

fn main() {
    // turn on to test the old code
    // test_binary_tree();
    test_binary_search_tree();
}

fn test_binary_search_tree() {
    let rootlink: BstNodeLink = BstNode::new_bst_nodelink(15);
    rootlink.borrow_mut().add_left_child(&rootlink, 6);
    rootlink.borrow_mut().add_right_child(&rootlink, 18);

    //add right subtree
    let right_subtree: Option<BstNodeLink> = rootlink.borrow().right.clone();
    if let Some(ref right_tree_extract) = right_subtree {
        right_tree_extract
            .borrow_mut()
            .add_left_child(right_tree_extract, 17);
        right_tree_extract
            .borrow_mut()
            .add_right_child(right_tree_extract, 20);
    }

    //add left subtree
    let left_subtree: Option<BstNodeLink> = rootlink.borrow().left.clone();
    if let Some(ref left_tree_extract) = left_subtree {
        left_tree_extract
            .borrow_mut()
            .add_left_child(left_tree_extract, 3);
        left_tree_extract
            .borrow_mut()
            .add_right_child(left_tree_extract, 7);

        //add left subtree terminal
        let left_subtree_terminal = &left_tree_extract.borrow().left;
        if let Some(terminal_left_tree_link) = left_subtree_terminal {
            terminal_left_tree_link
                .borrow_mut()
                .add_left_child(terminal_left_tree_link, 2);
            terminal_left_tree_link
                .borrow_mut()
                .add_right_child(terminal_left_tree_link, 4);
        }
        //add 2nd level right subtree of node 7
        let second_right_subtree = &left_tree_extract.borrow().right;
        if let Some(second_right_subtree_link) = second_right_subtree {
            second_right_subtree_link
                .borrow_mut()
                .add_right_child(second_right_subtree_link, 13);

            let third_left_subtree = &second_right_subtree_link.borrow().right;
            if let Some(third_left_subtree_link) = third_left_subtree {
                third_left_subtree_link
                    .borrow_mut()
                    .add_left_child(third_left_subtree_link, 9);
            }
        }
    }

    // print the tree at this time
    // i have opted to use my custom tree-printing algorithm defined in tool/mod.rs, as it's more comfortable to use (in my opinion)
    let mut main_tree_path: &str = "bst_graph.dot";
    generate_dotfile_bst_better(&rootlink, main_tree_path);
    println!("");
    print_graph(&rootlink);

    //tree search test
    let search_keys: Vec<i32> = vec![15, 9, 22];

    for &key in search_keys.iter() {
        print!("tree search result of key {} is ", key);
        if let Some(node_result) = rootlink.borrow().tree_search(&key) {
            println!("found -> {:?}", node_result.borrow().key);
        } else {
            println!("not found");
        }
    }

    //min test
    let min_node: std::rc::Rc<std::cell::RefCell<BstNode>> = rootlink.borrow().minimum();
    println!("minimum result {:?}", min_node.borrow().key);

    //max test
    let max_node: std::rc::Rc<std::cell::RefCell<BstNode>> = rootlink.borrow().maximum();
    println!("maximum result {:?}", max_node.borrow().key);

    //root node get test
    let root_node: std::rc::Rc<std::cell::RefCell<BstNode>> = BstNode::get_root(&max_node);
    println!("");
    println!("root node {:?}", root_node.borrow().key);

    //successor test
    let query_keys: Vec<i32> = vec![
        2,  // min_node, should return its parent Some(3)
        20, // max_node, should return None
        15, // root_node, should return the minimum of its right tree
        // test case for node with empty right child
        // should return a parent of the node's ancestor if it's a left child of the parent
        13, 9, 7,  // other keys
        22, // non-existent key
    ];

    for &key in query_keys.iter() {
        if let Some(node) = rootlink.borrow().tree_search(&key) {
            print!("successor of node ({}) is ", key);

            if let Some(successor) = BstNode::tree_successor_simpler(&node) {
                println!("{:?}", successor.borrow().key);
            } else {
                println!("not found");
            }
        } else {
            println!(
                "node with key of {} does not exist, failed to get successor",
                key
            )
        }
    }
    let keys_to_insert: Vec<i32> = vec![1, 5, 8, 10, 11, 12, 14, 16, 19, 21, 30, 25, 27];
    for &key in keys_to_insert.iter() {
        let inserted: Option<BstNodeLink> = BstNode::tree_insert(&rootlink, &key);
        println!(
            "Inserted a node with the i32-typed key value of {}: {:?}",
            key, inserted
        );
    }
    let duplicate: Option<BstNodeLink> = BstNode::tree_insert(&rootlink, &8);
    println!("Attempt to insert duplicate key 8: {:?}", duplicate); // should theoretically return None, as 8 has already been inserted into the binary search tree.

    // output the current state of the binary search tree after testing the insertion algorithm, both into stdout and to a .dot file using BufWriter<File>
    main_tree_path = "bst_graph_2.dot";
    generate_dotfile_bst_better(&rootlink, main_tree_path);
    println!("");
    print_graph(&rootlink);

    // test the transplant function
    // This operation should theoretically move node 9 up to where node 13 was.
    // That way, it replaces the subtree rooted at node u, with the subtree rooted at node v.
    let node_13: Rc<std::cell::RefCell<BstNode>> = rootlink.borrow().tree_search(&13).unwrap();
    let node_9: Rc<std::cell::RefCell<BstNode>> = rootlink.borrow().tree_search(&9).unwrap();

    let result: bool = rootlink
        .borrow_mut()
        .transplant(&node_13.clone(), &Some(node_9.clone()));

    if result {
        println!("Transplanted node 13 with node 9 successfully.");
        println!("Node 13 has been successfully replaced with node 9.");
        // After transplanting node u with node v, we should take care to relink v's children's parent pointers back to v.
        // After careful consideration and much thinking, it turns out that I'm really really not supposed to integrate this logic into the transplant() function.
        // Specifically, this is because the CLRS book says "Note that TRANSPLANT does not attempt to update v.left and v.right; doing so is the responsibility of TRANSPLANT’s caller."
        // Which means, that this kind of necessary operation should be manually handled in the function caller's scope.
        // the tree_delete() function also seems to already do this as well.
        // so whatever.
        if let Some(ref left_children) = node_9.borrow().left {
            left_children.borrow_mut().parent = Some(Rc::downgrade(&node_9));
        }
        if let Some(ref right_children) = node_9.borrow().right {
            right_children.borrow_mut().parent = Some(Rc::downgrade(&node_9));
        }
    } else {
        println!("Failed to transplant node 13 with node 9.");
    }

    // output the current state of the binary search tree after transplanting node 13 with node 9.
    // both to stdout and to a graphviz dot notation .dot file.
    main_tree_path = "bst_graph_after_transplant.dot";
    generate_dotfile_bst_better(&rootlink, main_tree_path);
    print_graph(&rootlink);

    // test the tree_delete function by deleting node 7, passing the Rc<RefCell<BstNode>> into the function as parameter.
    // in order to get that Rc<RefCell<BstNode>>, i'm using a customly-defined tree_search_rc_iterative function that i
    // manually wrote in structure/bst.rs.
    // both tree_search_rc_iterative and tree_search_rc_recursive allows us to get the node by getting a clone of the
    // Rc<RefCell<BstNode>> WITHOUT cloning self (which is of type BstNode) first and then wrapping it inside an Rc<RefCell<T>> (which actually doesn't work as expected and actually caused me the deletion bugs).
    // this will help me TREMENDOUSLY in the tree_delete_with_key test after this one.
    let node_7: Rc<std::cell::RefCell<BstNode>> =
        BstNode::tree_search_rc_iterative(&rootlink, &7).unwrap();
    let mut delete_result: bool = rootlink.borrow_mut().tree_delete(&node_7);
    if delete_result {
        println!("Deleted node 7 successfully.");
    } else {
        println!("Failed to delete node 7.");
    }

    // print the current state of the BST both into stdout and to a .dot file for png image generation
    main_tree_path = "bst_graph_after_deleting_7_by_bst_node_link.dot";
    generate_dotfile_bst_better(&rootlink, main_tree_path);
    print_graph(&rootlink);

    // test tree_delete_with_key() function by first defining a Vec<i32> that consists of the numbers of the nodes that I want to delete.
    // The numbers of the nodes that I want to delete consists of various test cases and whatnot.
    let keys_to_delete: Vec<i32> = vec![
        1, // leaf node, is a left children to its parent (2) || FINALLY WORKS AFTER CODE DEBUGGING AND REWRITING, previously it used to still show 1 on the generated image, which doesn't make any sense
        16, // leaf node, is a left children to its parent (17) || FINALLY WORKS AFTER CODE DEBUGGING AND REWRITING, previously it used to still show 16 on the generated image, which also doesn't make sense
        5,  // leaf node, is a right children to its parent (4) // WORKS
        12, // leaf node, is a right children to its parent (11) // WORKS
        2, // has a left child, is itself a left child to its parent (3) // FINALLY WORKS AFTER CODE DEBUGGING AND REWRITING
        10, // has a right child, is itself a right child to its parent (10) // PERFECTLY WORKS JUST FINE OUT OF THE BOX, this is the same case as with the deletion of node 7 above, which also works perfectly fine.
        3, // has both a left and a right child, is itself a left child to its parent, which is (6) // FINALLY WORKS AFTER CODE DEBUGGING AND REWRITING
        20, // has both a left and a right child, but is itself a right child to its parent, which is (18) // FINALLY WORKS NOW AFTER CODE DEBUGGING AND REWRITING
        25, // has a right child, is itself a left child to its parent, which is node 30.
        30, // after deleting 25, node 30 would still have a left child, is itself a right child to its parent, which is node 21.
    ];

    // iterate over every i32 in the defined Vec<i32> above, deleting the currently-iterated i32 in each iteration.
    for &key in keys_to_delete.iter() {
        delete_result = BstNode::tree_delete_with_key(&rootlink, &key);
        if delete_result {
            // if the deletion is successfull, we print this
            println!("Deleted node with key {} successfully.", key);
        } else {
            // if not print this
            println!("Failed to delete node with key {}.", key);
        }
    }

    // print the tree after deleting certain keys.
    main_tree_path = "bst_graph_after_deleting_certain_keys_by_i32_value.dot";
    generate_dotfile_bst_better(&rootlink, main_tree_path);
    print_graph(&rootlink);
}

#[allow(dead_code)]
fn test_binary_tree() {
    //create the nodelink of the root node
    let rootlink: NodeLink = Node::new_nodelink(5);

    //add a new left node value
    rootlink.borrow_mut().add_left_child(&rootlink, 3);
    //add a new right node value
    rootlink.borrow_mut().add_right_child(&rootlink, 7);

    //println!("{:?}", rootlink);

    //print the tree at this time
    let mut main_tree_path = "prime.dot";
    generate_dotfile(&rootlink, main_tree_path);

    //add new child values to the left subtree
    let left_subtree = &rootlink.borrow().left;
    if let Some(left_tree_extract) = left_subtree {
        left_tree_extract
            .borrow_mut()
            .add_left_child(left_tree_extract, 2);
        left_tree_extract
            .borrow_mut()
            .add_right_child(left_tree_extract, 4);
    }

    //add new child values to the right subtree
    let right_subtree = &rootlink.borrow().right;
    if let Some(right_tree_extract) = right_subtree {
        right_tree_extract
            .borrow_mut()
            .add_right_child(right_tree_extract, 10);
    }

    //print the tree again, now been added with more values
    main_tree_path = "prime_t2.dot";
    generate_dotfile(&rootlink, main_tree_path);

    //Call tree depth function at this time
    let recorded_depth = rootlink.borrow().tree_depth();
    println!("Current tree depth: {0}", recorded_depth);

    //Call count_nodes function
    let total_nodes = rootlink.borrow().count_nodes();
    println!("Amount of nodes in current tree: {0}", total_nodes);

    //Call count_nodes_by_nodelink function, supplied right subtree as parameter
    //TODO
    let subtree_count = Node::count_nodes_by_nodelink(&right_subtree.clone().unwrap(), 0);
    println!("Amount of nodes in current subtree: {0}", subtree_count);

    //Get the sibling of the leftsubtree from parent
    let _left_subtree_sibling = Node::get_sibling(&left_subtree.as_ref().unwrap());
    //println!("sibling of left subtree {:?}", left_subtree_sibling);

    //get the left subtree by value
    let left_subtree = rootlink.borrow().get_node_by_value(3);
    println!("left subtree seek by value {:?}", left_subtree);
    //get the left subtree by full properties
    let another_left_subtree = rootlink
        .borrow()
        .get_node_by_full_property(&left_subtree.as_ref().unwrap());
    println!(
        "left subtree seek by full property {:?}",
        another_left_subtree
    );

    //Discard the right subtree from parent
    let rootlink2 = rootlink.borrow().get_nodelink_copy();

    let flag = rootlink2.borrow_mut().discard_node_by_value(3);
    println!("status of node deletion: {0}", flag);

    //print the tree again
    main_tree_path = "prime_t3.dot";
    generate_dotfile(&rootlink2, main_tree_path);

    //Call tree depth function at this time
    //TODO
    let depth_now = rootlink2.borrow().tree_depth();
    println!("Depth after discard {0}", depth_now);

    //Call count_nodes function
    let count_now = rootlink2.borrow().count_nodes();
    println!("Count nodes after discard {0}", count_now);

    //print the tree again
    main_tree_path = "prime_t4.dot";
    generate_dotfile(&rootlink, main_tree_path);
}
