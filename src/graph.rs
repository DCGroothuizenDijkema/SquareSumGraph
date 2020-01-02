
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//
//                                                                                                                                       //
// graph.rs                                                                                                                              //
//                                                                                                                                       //
// D. C. Groothuizen Dijkema - January, 2020                                                                                             //
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//

// Graph theory related classes, traits, and impls


#![allow(dead_code)]
#![allow(unused_variables)]

use std::cell::RefCell;
use std::rc::Rc;
use std::vec::Vec;
use std::option::Option;
use std::result::Result;


//
// Traits
//

pub trait Scalar:
  std::cmp::PartialEq
  + std::marker::Copy
{
}

impl<T> Scalar for T where T:
  std::cmp::PartialEq
  + std::marker::Copy
{
}


//
// Structs
//

pub struct Node<T>
  where T: Scalar
{
  val: T,
  edges: Vec<Rc<RefCell<Edge<T>>>>,
}

impl<T> Node<T>
  where T: Scalar
{
  /// Returns a new Node with a given value and an empty Vec of Edges.
  /// 
  /// # Parameters
  /// * `val` : T
  ///   The value for the Node to take.
  /// 
  /// # Returns
  /// * `node` : Node<T>
  ///   A new Node with given value.
  pub fn new(val: T) -> Self
  {
    Node{val:val,edges:Vec::<Rc<RefCell<Edge<T>>>>::new()}
  }

  pub fn val(&self) -> T
  {
    self.val
  }
}

pub struct Edge<T>
  where T: Scalar
{
  nodes: Vec<Rc<RefCell<Node<T>>>>,
}

pub struct Graph<T>
  where T: Scalar
{
  nodes: Vec<Rc<RefCell<Node<T>>>>,
  edges: Vec<Rc<RefCell<Edge<T>>>>,
}

impl<T> Graph<T>
  where T: Scalar
{
  /// Returns a new Graph with an empty Vec of Nodes and Edges.
  /// 
  /// # Returns
  /// * `graph` : Graph<T>
  ///   A new Graph.
  pub fn new() -> Self
  {
    Graph{nodes:Vec::<Rc<RefCell<Node<T>>>>::new(),edges:Vec::<Rc<RefCell<Edge<T>>>>::new()}
  }

  /// Create a new Node with a given value and add it to the Graph.
  /// Cannot add a new Node with the same value as a Node already in the Graph.
  /// 
  /// # Parameters
  /// * `val` : T
  ///   The value for the Node to take.
  /// 
  /// # Returns
  /// * `res` : Result<Rc<RefCell<Node<T>>>,usize>
  ///   `res` is Result::Ok if the Node was added. res::OK contains an Rc<RefCell<>> to the Node.
  ///   `res` is Result::Err if the Node already exists. res::Err contains `val`.
  pub fn add_node(&mut self,val: T) -> Result<Rc<RefCell<Node<T>>>,T>
  {
    // check the Node doesn't already exist
    if self.find(val).is_some() { return Result::Err(val); }

    // construct the Node and the result from the NOde
    let nd: Rc<RefCell<Node<T>>>=Rc::new(RefCell::new(Node::new(val)));
    let res: Result<Rc<RefCell<Node<T>>>,T>=Result::Ok(Rc::clone(&nd));
    // add the Node to the Graph
    self.nodes.push(nd);
    res
  }

  /// Connect two Nodes in the Graph.
  /// 
  /// # Parameters
  /// * `val_one`,`val_two` : T
  ///   The values of the two Nodes to connect.
  /// 
  /// # Returns
  /// * `res` : Result<Rc<RefCell<Edge<T>>>,T>
  ///   `res` is Result::Ok if the Nodes were connected. res::OK contains an Rc<RefCell<>> to the Edge connecting the Nodes.
  ///   `res` is Result::Err if either of the Nodes do not exist. res::Err contains the first value which did not exist.
  pub fn connect(&mut self,val_one: T,val_two: T) -> Result<Rc<RefCell<Edge<T>>>,T>
  {
    // check both Nodes exist
    let node_one: Option<Rc<RefCell<Node<T>>>>=self.find(val_one);
    if node_one.is_none() { return Result::Err(val_one); }
    let node_two: Option<Rc<RefCell<Node<T>>>>=self.find(val_two);
    if node_two.is_none() { return Result::Err(val_two); }

    // retrieve the Nodes
    let node_one: Rc<RefCell<Node<T>>>=node_one.unwrap();
    let node_two: Rc<RefCell<Node<T>>>=node_two.unwrap();
    // construct the Edge from the two Nodes and the result from the Edge
    let edge: Rc<RefCell<Edge<T>>>=Rc::new(RefCell::new(Edge{nodes:vec![Rc::clone(&node_one),Rc::clone(&node_two)]}));
    let res: Result<Rc<RefCell<Edge<T>>>,T>=Result::Ok(Rc::clone(&edge));
    // add the Edge to the two Nodes
    node_one.borrow_mut().edges.push(Rc::clone(&edge));
    node_two.borrow_mut().edges.push(Rc::clone(&edge));
    // add the Edge to the Graph
    self.edges.push(edge);
    res
  }

  /// Find a node in the Graph
  /// 
  /// # Parameters
  /// * `val` : T
  ///   The value of the Node to find.
  /// 
  /// # Returns
  /// * `res` : Option<Rc<RefCell<Node<T>>>>
  ///   `res` is Option::Some if the Node was found. res::Some contains an Rc<RefCell<>> to the Node.
  ///   `res` is Option::None if the Node could not be found.
  pub fn find(&self,val: T) -> Option<Rc<RefCell<Node<T>>>>
  {
    for node in &self.nodes
    {
      if node.borrow().val==val { return Option::Some(Rc::clone(&node)); }
    }
    Option::None
  }
}


//
// Tests
//

#[cfg(test)]
mod node_tests
{
  use super::Node;

  #[test]
  fn test_new()
  {
    let node=Node::<i32>::new(0);
    assert!(node.val==0);
    assert!(node.edges.is_empty());
    let node=Node::<bool>::new(true);
    assert!(node.val==true);
    assert!(node.edges.is_empty());
    let node=Node::<f64>::new(3.14);
    assert!(node.val==3.14);
    assert!(node.edges.is_empty());
    let node=Node::<char>::new('c');
    assert!(node.val=='c');
    assert!(node.edges.is_empty());
  }
}

#[cfg(test)]
mod graph_tests
{
  use super::{Rc,Option,Result,RefCell};
  use super::{Graph,Node,Edge};

  #[test]
  fn test_new()
  {
    let graph=Graph::<usize>::new();
    assert!(graph.nodes.is_empty());
    assert!(graph.edges.is_empty());
  }

  #[test]
  fn test_add_node()
  {
    // test a valid insertion
    let mut graph=Graph::<usize>::new();
    let res: Result<Rc<RefCell<Node<usize>>>,usize>=graph.add_node(2);
    assert!(res.is_ok());
    match res
    {
      Ok(x) => assert!(x.borrow().val==2),
      _     => (),
    }
    assert!(graph.nodes[0].borrow().val==2);
    assert!(graph.nodes.len()==1);
    
    // test an invalid insertion
    let res: Result<Rc<RefCell<Node<usize>>>,usize>=graph.add_node(2);
    assert!(res.is_err());
    match res
    {
      Err(x) => assert!(x==2),
      _     => (),
    }
    assert!(graph.nodes.len()==1);

    // test another valid insertion
    let res: Result<Rc<RefCell<Node<usize>>>,usize>=graph.add_node(1729);
    assert!(res.is_ok());
    match res
    {
      Ok(x) => assert!(x.borrow().val==1729),
      _     => (),
    }
    assert!(graph.nodes.len()==2);
    assert!(graph.nodes[1].borrow().val==1729);
  }

  #[test]
  fn test_find()
  {
    let vals: [f64;5]=[3.14,2.72,1.20,1.62,1.64];
    let mut graph=Graph::<f64>::new();
    
    // add the values
    for &val in vals.iter()
    {
      graph.add_node(val).unwrap();
    }
    // values that have been added can be found
    for &val in vals.iter()
    {
      let res: Option<Rc<RefCell<Node<f64>>>>=graph.find(val);
      assert!(res.is_some());
      let nd: Rc<RefCell<Node<f64>>>=res.unwrap();
      assert!(nd.borrow().val==val);
    }
    // a value that hasn't been added cannot be found
    let res: Option<Rc<RefCell<Node<f64>>>>=graph.find(2.93);
    assert!(res.is_none());
  }

  #[test]
  fn test_connect()
  {
    // test error when no nodes are added
    let mut graph=Graph::<i32>::new();
    let res: Result<Rc<RefCell<Edge<i32>>>,i32>=graph.connect(173,-98);
    assert!(res.is_err());
    // the Err Result should be the first value
    match res
    {
      Err(x) => assert!(x==173),
      _      => (),
    }
    assert!(graph.edges.is_empty());
    
    // test error when one node has been added
    let nd_one: Rc<RefCell<Node<i32>>>=graph.add_node(173).unwrap();
    let res: Result<Rc<RefCell<Edge<i32>>>,i32>=graph.connect(173,-98);
    assert!(res.is_err());
    // the Err Result should be the second value
    match res
    {
      Err(x) => assert!(x==-98),
      _      => (),
    }
    assert!(graph.edges.is_empty());

    // test no error when both nodes have been added
    let nd_two: Rc<RefCell<Node<i32>>>=graph.add_node(-98).unwrap();
    let res: Result<Rc<RefCell<Edge<i32>>>,i32>=graph.connect(173,-98);
    assert!(graph.edges.len()==1); // one edge should have been added
    assert!(res.is_ok()); // Result should be Ok
    let edge_one: Rc<RefCell<Edge<i32>>>=res.unwrap();
    // Nodes should have been added to Edge in order
    assert!(&*nd_one.borrow() as *const Node<i32> == &*edge_one.borrow().nodes[0].borrow() as *const Node<i32>);
    assert!(&*nd_two.borrow() as *const Node<i32> == &*edge_one.borrow().nodes[1].borrow() as *const Node<i32>);
    
    // test no error when both nodes have been added
    let nd_three: Rc<RefCell<Node<i32>>>=graph.add_node(1).unwrap();
    let res: Result<Rc<RefCell<Edge<i32>>>,i32>=graph.connect(173,1);
    assert!(graph.edges.len()==2); // one edge should have been added
    assert!(res.is_ok()); // Result should be Ok
    let edge_two: Rc<RefCell<Edge<i32>>>=res.unwrap();
    // Nodes should have been added to Edge in order
    assert!(&*nd_one.borrow() as *const Node<i32> == &*edge_two.borrow().nodes[0].borrow() as *const Node<i32>);
    assert!(&*nd_three.borrow() as *const Node<i32> == &*edge_two.borrow().nodes[1].borrow() as *const Node<i32>);

    // check matches
    assert!(&*graph.nodes[0].borrow() as *const Node<i32> == &*graph.edges[0].borrow().nodes[0].borrow() as *const Node<i32>); 
    assert!(&*graph.nodes[0].borrow() as *const Node<i32> == &*graph.edges[1].borrow().nodes[0].borrow() as *const Node<i32>); 
    assert!(&*graph.nodes[1].borrow() as *const Node<i32> == &*graph.edges[0].borrow().nodes[1].borrow() as *const Node<i32>); 
    assert!(&*graph.nodes[2].borrow() as *const Node<i32> == &*graph.edges[1].borrow().nodes[1].borrow() as *const Node<i32>);

    // check matches
    assert!(&*nd_one.borrow().edges[0].borrow() as *const Edge<i32> == &*edge_one.borrow()  as *const Edge<i32>);
    assert!(&*nd_one.borrow().edges[1].borrow() as *const Edge<i32> == &*edge_two.borrow()  as *const Edge<i32>);
    assert!(&*nd_two.borrow().edges[0].borrow() as *const Edge<i32> == &*edge_one.borrow()  as *const Edge<i32>);
    assert!(&*nd_three.borrow().edges[0].borrow() as *const Edge<i32> == &*edge_two.borrow()  as *const Edge<i32>);
  }
}