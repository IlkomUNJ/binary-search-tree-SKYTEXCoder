pub mod bst;
pub mod tree {
    use std::cell::RefCell;
    use std::rc::{Rc, Weak};

    pub type NodeLink = Rc<RefCell<Node>>;
    pub type WeakNodeLink = Weak<RefCell<Node>>;

    #[derive(Debug, Clone)]
    pub struct Node {
        pub value: i32,
        pub parent: Option<Weak<RefCell<Node>>>,
        pub left: Option<NodeLink>,
        pub right: Option<NodeLink>,
    }

    impl Node {
        //private interface
        fn new(value: i32) -> Self {
            Node {
                value,
                left: None,
                right: None,
                parent: None,
            }
        }

        pub fn new_nodelink(value: i32) -> NodeLink {
            let currentnode: Node = Node::new(value);
            let currentlink: Rc<RefCell<Node>> = Rc::new(RefCell::new(currentnode));
            currentlink
        }

        /**
         * Consumptive, this function can only be called once for the whole lifetime
         */
        #[allow(dead_code)]
        fn get_nodelink(self) -> NodeLink {
            Rc::new(RefCell::new(self))
        }

        /**
         * Get a copy of node link
         */
        pub fn get_nodelink_copy(&self) -> NodeLink {
            Rc::new(RefCell::new(self.clone()))
        }

        //private interface
        fn new_with_parent(parent: &NodeLink, value: i32) -> NodeLink {
            let mut currentnode: Node = Node::new(value);
            currentnode.add_parent(Rc::<RefCell<Node>>::downgrade(parent));
            let currentlink: Rc<RefCell<Node>> = Rc::new(RefCell::new(currentnode));
            currentlink
        }

        fn new_from_node(node: Node) -> NodeLink {
            let currentlink: Rc<RefCell<Node>> = Rc::new(RefCell::new(node));
            currentlink
        }

        //add new left child, set the parent to current_node_link
        pub fn add_left_child(&mut self, current_node_link: &NodeLink, value: i32) {
            let new_node: Rc<RefCell<Node>> = Node::new_with_parent(current_node_link, value);
            self.left = Some(new_node);
        }

        //add new right child, set the parent to current_node_link
        pub fn add_right_child(&mut self, current_node_link: &NodeLink, value: i32) {
            let new_node: Rc<RefCell<Node>> = Node::new_with_parent(current_node_link, value);
            self.right = Some(new_node);
        }

        //unused
        fn add_parent(&mut self, node: WeakNodeLink) {
            self.parent = Some(node);
        }

        /**
         * As the name implied, used to upgrade parent node to strong nodelink
         */
        pub fn upgrade_weak_to_strong(node: Option<WeakNodeLink>) -> Option<NodeLink> {
            match node {
                None => None,
                Some(x) => Some(x.upgrade().unwrap()),
            }
        }

        /**
         * Unused
         */
        #[allow(dead_code)]
        fn is_node_match_weak_strong(node1: Option<WeakNodeLink>, node2: Option<NodeLink>) -> bool {
            let node1s: Option<Rc<RefCell<Node>>> = Node::upgrade_weak_to_strong(node1);
            if node1s.is_none() && node2.is_none() {
                return true;
            }
            if let Some(node1sv) = node1s {
                return node2.is_some_and(|x: NodeLink| x.borrow().value == node1sv.borrow().value);
            }
            false
        }

        //helper function
        fn is_node_match_both_weak(
            node1: Option<WeakNodeLink>,
            node2: Option<WeakNodeLink>,
        ) -> bool {
            let node1s: Option<Rc<RefCell<Node>>> = Node::upgrade_weak_to_strong(node1);
            let node2s: Option<Rc<RefCell<Node>>> = Node::upgrade_weak_to_strong(node2);
            if node1s.is_none() && node2s.is_none() {
                return true;
            }
            return Node::is_node_match_both_strong(node1s, node2s);
        }

        //helper function to compare both nodelink
        fn is_node_match_both_strong(node1: Option<NodeLink>, node2: Option<NodeLink>) -> bool {
            if node1.is_none() && node2.is_none() {
                return true;
            }
            if let Some(node1v) = node1 {
                return node2.is_some_and(|x: NodeLink| x.borrow().value == node1v.borrow().value);
            }
            return false;
        }

        /**
         * This function will return the node that match value
         * Let's assume the tree won't have any value duplicates
         */
        pub fn get_node_by_value(&self, value: i32) -> Option<NodeLink> {
            //check current node value
            if self.value == value {
                //create clone of NodeLink
                let node: Node = self.clone();
                let nodelink: Rc<RefCell<Node>> = Rc::new(RefCell::new(node));
                return Rc::<RefCell<Node>>::downgrade(&nodelink).upgrade();
            }
            //go left if exist
            if let Some(x) = &self.left {
                return x.borrow().get_node_by_value(value);
            }
            if let Some(x) = &self.right {
                return x.borrow().get_node_by_value(value);
            }
            return None;
        }

        /**
         * This function will return the node that matches all Nodelink Properties:
         * 1). current node value,
         * 2). node parent value,
         * 3). both child values
         * Let's assume the tree won't have any value duplicates
         * Asssume 2nd parameter is not None
         */
        pub fn get_node_by_full_property(&self, node: &NodeLink) -> Option<NodeLink> {
            //check current node value
            let nodevalue: i32 = node.borrow().value;
            let check_parent_eq: bool =
                Node::is_node_match_both_weak(node.borrow().parent.clone(), self.parent.clone());
            let check_left_child_eq: bool =
                Node::is_node_match_both_strong(node.borrow().left.clone(), self.left.clone());
            let check_right_child_eq: bool =
                Node::is_node_match_both_strong(node.borrow().right.clone(), self.right.clone());
            if self.value == nodevalue
                && check_parent_eq
                && check_left_child_eq
                && check_right_child_eq
            {
                return Some(self.get_nodelink_copy());
            } else {
                //recurse deeper if not found
                //recurse to left
                if let Some(left_subtree) = &self.left {
                    return left_subtree.borrow().get_node_by_full_property(node);
                } else if let Some(right_subtree) = &self.right {
                    //recurse to right
                    return right_subtree.borrow().get_node_by_full_property(node);
                }
            }
            None
        }

        /**
         * This function will discard a node that match the value, the whole node tree that match the description will be discarded
         * Along with its child
         * The concept how we discard the node is, if the current node match sever the connection with parent,
         * Then after return from the completion of immediate recursive, sever the connection with the child
         */
        pub fn discard_node_by_value(&mut self, value: i32) -> bool {
            //check current node value
            if self.value == value {
                //cut off parent connection
                self.parent = None;
                return true;
            } else if let Some(left_node) = &self.left {
                let result_flag: bool = left_node.borrow_mut().discard_node_by_value(value);
                //cut this child connection
                self.left = None;
                return result_flag;
            } else if let Some(right_node) = &self.right {
                let result_flag: bool = right_node.borrow_mut().discard_node_by_value(value);
                self.right = None;
                return result_flag;
            }
            false
        }

        /**
         * Count the amount of nodes in the whole subtree, in the current node
         * assume when enter the function the current node isn't a null
         */
        pub fn count_nodes(&self) -> i32 {
            let mut count: i32 = 0;
            let nodelink: Rc<RefCell<Node>> = Node::new_from_node(self.clone());
            count = Node::count_nodes_by_nodelink(&nodelink, count);
            return count;
        }

        //the same as above except start the count from nodelink reference parameter
        pub fn count_nodes_by_nodelink(node: &NodeLink, count: i32) -> i32 {
            let mut left_count: i32 = 0;
            let mut right_count: i32 = 0;
            if let Some(left_child) = &node.borrow().left {
                left_count = Node::count_nodes_by_nodelink(&left_child, count);
            }
            if let Some(right_child) = &node.borrow().right {
                right_count = Node::count_nodes_by_nodelink(&right_child, count);
            }
            return count + left_count + right_count + 1;
        }

        /**Count depth of the tree in the current node
         * Count from root is started from 0
         */
        pub fn tree_depth(&self) -> i32 {
            let depth: i32 = 0;
            let nodelink: Rc<RefCell<Node>> = Node::new_from_node(self.clone());
            return self.track_depth(&nodelink, depth);
        }

        //track depth by traversing all nodes but returned depth count per path. The highest number will be returned
        fn track_depth(&self, node: &NodeLink, depth: i32) -> i32 {
            let mut left_depth: i32 = 0;
            let mut right_depth: i32 = 0;
            if let Some(left_child) = &node.borrow().left {
                left_depth = self.track_depth(left_child, depth) + 1;
            }

            if let Some(right_child) = &node.borrow().right {
                right_depth = self.track_depth(right_child, depth) + 1;
            }

            if left_depth > right_depth {
                return left_depth;
            }

            right_depth
        }

        /**
         * a node is guaranteed to have two childs at most, since this is a binary tree
         * a sibling is a node which has same direct parent
         */
        pub fn get_sibling(nodelink: &NodeLink) -> Option<NodeLink> {
            //traverse to parent if not a root node
            if nodelink.borrow().parent.is_some() {
                //upgrade to strong
                let strong_parent: Option<Rc<RefCell<Node>>> =
                    Node::upgrade_weak_to_strong(nodelink.borrow().parent.clone());
                //check from which child are we
                if let Some(sparent) = strong_parent {
                    //check if the left fits nodelink value (we're coming from the left)
                    if sparent
                        .borrow()
                        .left
                        .as_ref()
                        .is_some_and(|x: &Rc<RefCell<Node>>| {
                            x.borrow().value == nodelink.borrow().value
                        })
                    {
                        //return the right node
                        return sparent.clone().borrow().right.clone();
                    } else {
                        //means we're obviously coming from the right since this block is entered
                        return sparent.clone().borrow().left.clone();
                    }
                }
            }
            None
        }
    }
}
