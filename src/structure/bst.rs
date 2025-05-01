use std::cell::RefCell;
use std::rc::{Rc, Weak};

pub type BstNodeLink = Rc<RefCell<BstNode>>;
pub type WeakBstNodeLink = Weak<RefCell<BstNode>>;

//this package implement BST wrapper
#[derive(Debug, Clone)]
pub struct BstNode {
    pub key: Option<i32>,
    pub parent: Option<WeakBstNodeLink>,
    pub left: Option<BstNodeLink>,
    pub right: Option<BstNodeLink>,
}

impl BstNode {
    //private interface
    fn new(key: i32) -> Self {
        BstNode {
            key: Some(key),
            left: None,
            right: None,
            parent: None,
        }
    }

    fn new_with_rc_pointer(key: i32) -> BstNodeLink {
        Rc::new(RefCell::new(BstNode::new(key)))
    }

    pub fn new_bst_nodelink(value: i32) -> BstNodeLink {
        let currentnode: BstNode = BstNode::new(value);
        let currentlink: Rc<RefCell<BstNode>> = Rc::new(RefCell::new(currentnode));
        currentlink
    }

    /**
     * Get a copy of node link
     */
    pub fn get_bst_nodelink_copy(&self) -> BstNodeLink {
        Rc::new(RefCell::new(self.clone()))
    }

    fn downgrade(node: &BstNodeLink) -> WeakBstNodeLink {
        Rc::downgrade(node)
    }

    //private interface
    fn new_with_parent(parent: &BstNodeLink, value: i32) -> BstNodeLink {
        let mut currentnode: BstNode = BstNode::new(value);
        //currentnode.add_parent(Rc::<RefCell<BstNode>>::downgrade(parent));
        currentnode.parent = Some(BstNode::downgrade(parent));
        let currentlink: Rc<RefCell<BstNode>> = Rc::new(RefCell::new(currentnode));
        currentlink
    }

    fn clone_rc_node(node: &BstNodeLink) -> BstNodeLink {
        Rc::clone(node)
    }

    fn clone_optional_node(optional_node: &Option<BstNodeLink>) -> Option<BstNodeLink> {
        optional_node.as_ref().map(Self::clone_rc_node)
    }

    fn clone_weak_node(weak_node: &WeakBstNodeLink) -> WeakBstNodeLink {
        Weak::clone(weak_node)
    }

    fn clone_optional_weak_bst_node(
        optional_weak_bst_node: &Option<WeakBstNodeLink>,
    ) -> Option<WeakBstNodeLink> {
        optional_weak_bst_node.as_ref().map(Self::clone_weak_node)
    }

    /**
     * As the name implied, used to upgrade parent node to strong nodelink
     */
    fn upgrade_weak_to_strong(node: Option<WeakBstNodeLink>) -> Option<BstNodeLink> {
        match node {
            None => None,
            Some(x) => Some(x.upgrade().unwrap()),
        }
    }

    fn downgrade_strong_to_weak(optional_node: Option<BstNodeLink>) -> Option<WeakBstNodeLink> {
        match optional_node {
            None => None,
            Some(x) => Some(Rc::downgrade(&x)),
        }
    }

    //add new left child, set the parent to current_node_link
    pub fn add_left_child(&mut self, current_node_link: &BstNodeLink, value: i32) {
        let new_node: Rc<RefCell<BstNode>> = BstNode::new_with_parent(current_node_link, value);
        self.left = Some(new_node);
    }

    //add new left child, set the parent to current_node_link
    pub fn add_right_child(&mut self, current_node_link: &BstNodeLink, value: i32) {
        let new_node: Rc<RefCell<BstNode>> = BstNode::new_with_parent(current_node_link, value);
        self.right = Some(new_node);
    }

    //search the current tree which node fit the value
    pub fn tree_search(&self, value: &i32) -> Option<BstNodeLink> {
        if let Some(key) = self.key {
            if key == *value {
                return Some(self.get_bst_nodelink_copy());
            }
            if *value < key && self.left.is_some() {
                return self.left.as_ref().unwrap().borrow().tree_search(value);
            } else if *value > key && self.right.is_some() {
                return self.right.as_ref().unwrap().borrow().tree_search(value);
            }
        }
        //default if current node is NIL
        None
    }

    pub fn tree_search_quiz(&self, value: &i32) -> Option<BstNodeLink> {
        match self.key {
            Some(key) if key == *value => Some(self.get_bst_nodelink_copy()),
            Some(key) if *value < key => {
                if let Some(ref left_node) = self.left {
                    left_node.borrow().tree_search_quiz(value)
                } else {
                    None
                }
            }
            Some(key) if *value > key => {
                if let Some(ref right_node) = self.right {
                    right_node.borrow().tree_search_quiz(value)
                } else {
                    None
                }
            }
            Some(_) => None,
            None => None,
        }
    }

    pub fn tree_search_rc_iterative(node: &BstNodeLink, value: &i32) -> Option<BstNodeLink> {
        let mut current_node: Option<BstNodeLink> = Some(BstNode::clone_rc_node(node));
        while let Some(ref current_node_rc) = current_node {
            let current_node_rc_clone: Rc<RefCell<BstNode>> = current_node_rc.clone();
            let current_key: i32 = current_node_rc_clone.borrow().key.unwrap();
            if *value == current_key {
                return Some(current_node_rc_clone);
            } else if *value < current_key {
                current_node = BstNode::clone_optional_node(&current_node_rc_clone.borrow().left);
            } else {
                current_node = BstNode::clone_optional_node(&current_node_rc_clone.borrow().right);
            }
        }
        None
    }

    pub fn tree_search_rc_recursive(node: &BstNodeLink, value: &i32) -> Option<BstNodeLink> {
        let key: i32 = node.borrow().key?;
        if key == *value {
            return Some(node.clone());
        }
        if *value < key {
            if let Some(ref left_children) = node.borrow().left {
                return BstNode::tree_search_rc_recursive(left_children, value);
            }
        } else if *value > key {
            if let Some(ref right_children) = node.borrow().right {
                return BstNode::tree_search_rc_recursive(right_children, value);
            }
        }
        None
    }

    /**seek minimum by recurs
     * in BST minimum always on the left
     */
    pub fn minimum(&self) -> BstNodeLink {
        if self.key.is_some() {
            if let Some(left_node) = &self.left {
                return left_node.borrow().minimum();
            }
        }
        self.get_bst_nodelink_copy()
    }

    pub fn minimum_quiz(&self) -> BstNodeLink {
        let mut current_node: Rc<RefCell<BstNode>> = self.get_bst_nodelink_copy();
        loop {
            let left_node: Option<Rc<RefCell<BstNode>>> = current_node.borrow().left.clone();
            if let Some(left_node_rc) = left_node {
                current_node = left_node_rc;
            } else {
                break;
            }
        }
        return current_node;
    }

    pub fn maximum(&self) -> BstNodeLink {
        if self.key.is_some() {
            if let Some(right_node) = &self.right {
                return right_node.borrow().maximum();
            }
        }
        self.get_bst_nodelink_copy()
    }

    pub fn maximum_quiz(&self) -> BstNodeLink {
        let mut current_node: Rc<RefCell<BstNode>> = self.get_bst_nodelink_copy();
        loop {
            let right_node: Option<Rc<RefCell<BstNode>>> = current_node.borrow().right.clone();
            if let Some(right_node_rc) = right_node {
                current_node = right_node_rc;
            } else {
                break;
            }
        }
        return current_node;
    }

    /**
     * Return the root of a node, return self if not exist
     */
    pub fn get_root(node: &BstNodeLink) -> BstNodeLink {
        let parent: Option<Rc<RefCell<BstNode>>> =
            BstNode::upgrade_weak_to_strong(node.borrow().parent.clone());
        if parent.is_none() {
            return node.clone();
        }
        return BstNode::get_root(&parent.unwrap());
    }

    /**
     * NOTE: Buggy from pull request
     * Find node successor according to the book
     * Should return None, if x_node is the highest key in the tree
     */

    pub fn tree_successor(x_node: &BstNodeLink) -> Option<BstNodeLink> {
        // directly check if the node has a right child, otherwise go to the next block
        if let Some(right_node) = &x_node.borrow().right {
            return Some(right_node.borrow().minimum());
        }
        // empty right child case
        else {
            let mut x_node: &Rc<RefCell<BstNode>> = x_node;
            let mut y_node: Option<Rc<RefCell<BstNode>>> =
                BstNode::upgrade_weak_to_strong(x_node.borrow().parent.clone());
            let mut temp: Option<BstNodeLink>; // Change type to Option<BstNodeLink>
            while let Some(ref exist) = y_node {
                if let Some(ref left_child) = exist.borrow().left {
                    if BstNode::is_node_match(left_child, x_node) {
                        return Some(exist.clone());
                    }
                }
                temp = Some(y_node.unwrap());
                x_node = temp.as_ref().unwrap();
                y_node =
                    BstNode::upgrade_weak_to_strong(temp.as_ref().unwrap().borrow().parent.clone());
            }
            None
        }
    }

    /**
     * Alternate simpler version of tree_successor that made use of is_nil checking
     */

    pub fn tree_successor_simpler(x_node: &BstNodeLink) -> Option<BstNodeLink> {
        //create a shadow of x_node so it can mutate
        let mut x_node: &Rc<RefCell<BstNode>> = x_node;
        let right_node: &Option<Rc<RefCell<BstNode>>> = &x_node.borrow().right.clone();
        if BstNode::is_nil(right_node) != true {
            return Some(right_node.clone().unwrap().borrow().minimum());
        }
        let mut y_node: Option<Rc<RefCell<BstNode>>> =
            BstNode::upgrade_weak_to_strong(x_node.borrow().parent.clone());
        let y_node_right: &Option<Rc<RefCell<BstNode>>> =
            &y_node.clone().unwrap().borrow().right.clone();
        let mut y_node2: Rc<RefCell<BstNode>>;
        while BstNode::is_nil(&y_node)
            && BstNode::is_node_match_option(Some(x_node.clone()), y_node_right.clone())
        {
            y_node2 = y_node.clone().unwrap();
            x_node = &y_node2;
            let y_parent: Weak<RefCell<BstNode>> =
                y_node.clone().unwrap().borrow().parent.clone().unwrap();
            y_node = BstNode::upgrade_weak_to_strong(Some(y_parent));
        }
        //in case our successor traversal yield root, means self is the highest key
        if BstNode::is_node_match_option(y_node.clone(), Some(BstNode::get_root(&x_node))) {
            return None;
        }
        //defaultly return self / x_node
        return Some(y_node.clone().unwrap());
    }

    pub fn tree_successor_quiz(x_node: &BstNodeLink) -> BstNodeLink {
        let x_borrow: std::cell::Ref<'_, BstNode> = x_node.borrow();
        if let Some(ref right_node) = x_borrow.right {
            return right_node.borrow().minimum_quiz();
        } else {
            let mut current_node: Rc<RefCell<BstNode>> = x_node.clone();
            let mut optional_parent: Option<Rc<RefCell<BstNode>>> = x_borrow
                .parent
                .clone()
                .and_then(|weak: Weak<RefCell<BstNode>>| weak.upgrade());
            while let Some(parent_rc_pointer) = optional_parent {
                let parent_borrow: std::cell::Ref<'_, BstNode> = parent_rc_pointer.borrow();
                if let Some(ref left_node) = parent_borrow.left {
                    if Rc::ptr_eq(left_node, &current_node) {
                        return parent_rc_pointer.clone();
                    }
                }
                current_node = parent_rc_pointer.clone();
                optional_parent = parent_borrow.parent.clone().and_then(|weak| weak.upgrade());
            }
        }
        return x_node.clone();
    }

    /// Inserts a new node with the given key into the BST.
    ///
    /// # Arguments
    ///
    /// * `bst_node_link` - Reference to the root node of the BST.
    /// * `key` - The key value to insert.
    ///
    /// # Returns
    ///
    /// * `Some(BstNodeLink)` if the insertion is successful.
    /// * `None` if a node with the same key already exists.
    pub fn tree_insert(bst_node_link: &BstNodeLink, key: &i32) -> Option<BstNodeLink> {
        if bst_node_link.borrow().tree_search(&key).is_some() {
            return None;
        }
        let z: BstNodeLink = BstNode::new_bst_nodelink(*key);
        z.borrow_mut().parent = None;
        z.borrow_mut().left = None;
        z.borrow_mut().right = None;
        let mut y: Option<BstNodeLink> = None;
        let mut x: Option<BstNodeLink> = Some(bst_node_link.clone());
        while let Some(x_rc_pointer) = x {
            y = Some(x_rc_pointer.clone());
            if z.borrow().key < x_rc_pointer.borrow().key {
                x = x_rc_pointer.borrow().left.clone();
            } else {
                x = x_rc_pointer.borrow().right.clone();
            }
        }
        if let Some(ref y_rc_pointer) = y {
            if z.borrow().key < y_rc_pointer.borrow().key {
                y_rc_pointer.borrow_mut().left = Some(z.clone());
            } else {
                y_rc_pointer.borrow_mut().right = Some(z.clone());
            }
            z.borrow_mut().parent = Some(Rc::downgrade(y_rc_pointer));
        } else {
            z.borrow_mut().parent = None;
            return Some(z.clone());
        }
        Some(z)
    }

    /// Replaces one subtree as a child of its parent with another subtree.
    ///
    /// # Arguments
    ///
    /// * `u` - The node to be replaced.
    /// * `v` - The node to replace `u` with (can be `None`).
    ///
    /// # Returns
    ///
    /// * `true` if the transplant operation is successful.
    /// * `false` if the parent pointer cannot be upgraded.
    pub fn transplant(&mut self, u: &BstNodeLink, v: &Option<BstNodeLink>) -> bool {
        if let Some(ref u_parent_weak_pointer) = &u.borrow().parent {
            if let Some(u_parent_rc_pointer) = u_parent_weak_pointer.upgrade() {
                let is_left_children: bool = if let Some(ref left_children) =
                    u_parent_rc_pointer.borrow().left
                {
                    Rc::ptr_eq(&u, left_children)
                } else {
                    Rc::ptr_eq(&u, &BstNode::new_bst_nodelink(i32::default())) // just compare it with some dummy nil node to make it return false to the boolean value of is_left_children
                };
                if is_left_children {
                    u_parent_rc_pointer.borrow_mut().left = v.clone();
                } else {
                    u_parent_rc_pointer.borrow_mut().right = v.clone();
                }
            } else {
                println!(
                    "The parent pointer cannot be upgraded. Exiting the transplanting operation."
                );
                return false;
            }
        } else {
            if let Some(ref v_rc_pointer) = &v {
                let v_node: std::cell::Ref<'_, BstNode> = v_rc_pointer.borrow();
                self.key = v_node.key;
                self.left = v_node.left.clone();
                self.right = v_node.right.clone();
                if let Some(ref left) = &self.left {
                    left.borrow_mut().parent = Some(Rc::downgrade(u));
                }
                if let Some(ref right) = &self.right {
                    right.borrow_mut().parent = Some(Rc::downgrade(u));
                }
            } else {
                println!("U's parent pointer and node V is both pointing to None. Nothing to do here, exiting the transplanting operation.");
                return true;
            }
        }
        if let Some(ref v_rc_pointer) = &v {
            v_rc_pointer.borrow_mut().parent =
                BstNode::clone_optional_weak_bst_node(&u.borrow().parent);
        }
        return true;
    }

    /// Deletes the specified node from the BST.
    ///
    /// # Arguments
    ///
    /// * `z` - The node to delete.
    ///
    /// # Returns
    ///
    /// * `true` if the deletion is successful.
    pub fn tree_delete(&mut self, z: &BstNodeLink) -> bool {
        if z.borrow().left.is_none() {
            self.transplant(z, &z.borrow().right.clone());
        } else if z.borrow().right.is_none() {
            self.transplant(z, &z.borrow().left.clone());
        } else {
            let successor: Rc<RefCell<BstNode>> =
                z.borrow().right.as_ref().unwrap().borrow().minimum();
            if !Rc::ptr_eq(&successor, z.borrow().right.as_ref().unwrap()) {
                self.transplant(&successor, &successor.borrow().right.clone());
                successor.borrow_mut().right = z.borrow().right.clone();
                if let Some(ref right) = successor.borrow().right {
                    right.borrow_mut().parent = Some(Rc::downgrade(&successor));
                }
            } else {
                successor.borrow_mut().right =
                    z.borrow().right.as_ref().unwrap().borrow().right.clone();
                if let Some(ref right_children) = successor.borrow().right {
                    right_children.borrow_mut().parent = Some(Rc::downgrade(&successor));
                }
            }
            self.transplant(z, &Some(successor.clone()));
            successor.borrow_mut().left = z.borrow().left.clone();
            if let Some(ref left) = successor.borrow().left {
                left.borrow_mut().parent = Some(Rc::downgrade(&successor));
            };
        }
        return true;
    }

    /// Deletes a node with the specified key from the BST.
    ///
    /// # Arguments
    ///
    /// * `key` - The key value of the node to delete.
    ///
    /// # Returns
    ///
    /// * `true` if the node is found and deleted.
    /// * `false` if the node with the given key does not exist.
    pub fn tree_delete_with_key(root: &BstNodeLink, key: &i32) -> bool {
        let node_to_delete: Option<Rc<RefCell<BstNode>>> =
            BstNode::tree_search_rc_iterative(root, key);
        if let Some(node) = node_to_delete {
            root.borrow_mut().tree_delete(&node);
            true
        } else {
            println!(
                "A node with the i32-typed key value of {} is not found inside this tree or subtree.",
                key
            );
            false
        }
    }

    /**
     * private function return true if node doesn't has parent nor children nor key
     */
    fn is_nil(node: &Option<BstNodeLink>) -> bool {
        match node {
            None => true,
            Some(x) => {
                if x.borrow().parent.is_none()
                    || x.borrow().left.is_none()
                    || x.borrow().right.is_none()
                {
                    return true;
                }
                return false;
            }
        }
    }

    //helper function to compare both nodelink
    fn is_node_match_option(node1: Option<BstNodeLink>, node2: Option<BstNodeLink>) -> bool {
        if node1.is_none() && node2.is_none() {
            return true;
        }
        if let Some(node1v) = node1 {
            return node2.is_some_and(|x: BstNodeLink| x.borrow().key == node1v.borrow().key);
        }
        return false;
    }

    fn is_node_match(anode: &BstNodeLink, bnode: &BstNodeLink) -> bool {
        if anode.borrow().key == bnode.borrow().key {
            return true;
        }
        return false;
    }
}
