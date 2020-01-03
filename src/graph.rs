
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
use std::collections::VecDeque;


//
// Traits
//

pub trait Scalar:
  std::cmp::PartialEq
  + std::marker::Copy
  + std::fmt::Display
  {
  }
  
  impl<T> Scalar for T where T:
  std::cmp::PartialEq
  + std::marker::Copy
  + std::fmt::Display
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

  pub fn degree(&self) -> usize
  {
    return self.edges.len()
  }

  pub fn is_isolated(&self) -> bool
  {
    return self.edges.len()==0
  }

  pub fn is_leaf(&self) -> bool
  {
    return self.edges.len()==1
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

  /// Returns true if the Graph has no Nodes, false otherwise
  pub fn is_empty(&self) -> bool
  {
    self.nodes.is_empty()
  }
  
  /// Returns true if the Graph has only one Node, false otherwise
  pub fn is_trivial(&self) -> bool
  {
    self.nodes.len()==1
  }
  
  /// Returns true if the Graph has only no Edges, false otherwise
  pub fn is_edgeless(&self) -> bool
  {
    self.edges.is_empty()
  }

  /// Returns the number of Nodes in the Graph
  pub fn order(&self) -> usize
  {
    self.nodes.len()
  }
  
  /// Returns the number of Edges in the Graph
  pub fn size(&self) -> usize
  {
    self.edges.len()
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
  ///   `res` is Result::Ok if the Nodes were is_connected. res::OK contains an Rc<RefCell<>> to the Edge connecting the Nodes.
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

    // check if the Nodes are already is_connected
    for edge in &node_one.borrow().edges
    {
      let node_one_val: T=node_one.borrow().val();
      let edge_node_zero_val: T=edge.borrow().nodes[0].borrow().val;
      let edge_node_one_val: T=edge.borrow().nodes[1].borrow().val;

      if edge_node_zero_val==node_one_val && edge_node_one_val==val_two { return Result::Err(edge_node_zero_val); }
      if edge_node_one_val==node_one_val && edge_node_zero_val==val_two { return Result::Err(edge_node_zero_val); }
    }

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

  /// Returns true if the Graph is connected, false otherwise
  pub fn is_connected(&self) -> bool
  {
    // trivial graph cases
    if self.is_empty() { return false; }
    if self.is_trivial() { return false; }
    if self.is_edgeless() { return false; }

    // very simple graphs
    if self.order()==2 && self.size()==1 { return true; }
    if self.order()==3 && self.size()>1 { return true; }

    // now just do a breath first search
    let mut visited: Vec<bool>=vec![false;self.order()];
    let mut q: VecDeque<Rc<RefCell<Node<T>>>>=VecDeque::<Rc<RefCell<Node<T>>>>::new();
    // add the first Noe and mark as visited
    q.push_back(Rc::clone(&self.nodes[0]));
    visited[0]=true;
    while !q.is_empty()
    {
      let nd: Rc<RefCell<Node<T>>>=q.pop_front().unwrap();  
      let nd_val: T=nd.borrow().val();
      // find all Nodes connected to the current Node
      for edge in &nd.borrow().edges
      {
        for connected_nd in &edge.borrow().nodes
        {
          let connected_val: T=connected_nd.borrow().val();
          // we may have found the current Node so continue
          if connected_val==nd_val { continue; }
          let idx: usize=self.get_idx(connected_val).unwrap();
          // if we haven't visited, mark as so, and add to search queue
          if !visited[idx]
          {
            visited[idx]=true;
            q.push_back(Rc::clone(&connected_nd));
          }
        }
      }
    }
    // if all of visited is true, the Graph is connected
    visited.iter().all(|&x| x==true)
  }

  pub fn hamiltonian_path(&self) -> Option<Vec<Rc<RefCell<Node<T>>>>>
  {
    if !self.is_connected() { return Option::None; }
    let mut degree_one_nodes_cnt: usize=0;

    // the Graph cannot have more than two Nodes with degree 1
    for nd in &self.nodes
    {
      if nd.borrow().is_leaf() { degree_one_nodes_cnt += 1; }
      if degree_one_nodes_cnt>2 { return Option::None; }
    }
    Option::None
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
  fn find(&self,val: T) -> Option<Rc<RefCell<Node<T>>>>
  {
    for nd in &self.nodes
    {
      if nd.borrow().val==val { return Option::Some(Rc::clone(&nd)); }
    }
    Option::None
  }

  /// Get the index of a node in a Graph
  /// 
  /// # Parameters
  /// * `val` : T
  ///   The value of the Node to find.
  /// 
  /// # Returns
  /// * `res` : Option<usize>
  ///   `res` is Option::Some if the Node was found. res::Some contains the index of the Node.
  ///   `res` is Option::None if the Node could not be found.
  fn get_idx(&self,val: T) -> Option<usize>
  {
    self.nodes.iter().position(|x| x.borrow().val()==val)
  }
}

impl<'a,T> std::iter::IntoIterator for &'a Graph<T>
  where T: Scalar
{
  type Item = &'a Rc<RefCell<Node<T>>>;
  type IntoIter = std::slice::Iter<'a,Rc<RefCell<Node<T>>>>;

  fn into_iter(self) -> std::slice::Iter<'a,Rc<RefCell<Node<T>>>>
  {
    self.nodes.iter()
  }
}

impl<T> std::fmt::Display for Graph<T>
  where T: Scalar
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
  {
    write!(f, "Nodes:\n  ");
    for (itr,nd) in self.nodes.iter().enumerate()
    {
      write!(f, "{}",nd.borrow().val());
      if itr!=self.order()-1 { write!(f, ","); }
    }
    write!(f, "\nEdges:\n  ");
    for (itr,ed) in self.edges.iter().enumerate()
    {
      write!(f, "{} -> {}",ed.borrow().nodes[0].borrow().val(),ed.borrow().nodes[1].borrow().val());
      if itr!=self.size()-1 { write!(f, ",\n  "); }
    }
    write!(f,"")
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
  fn test_get_idx()
  {
    let vals: [f64;5]=[3.14,2.72,1.20,1.62,1.64];
    let mut graph=Graph::<f64>::new();
    
    // add the values
    for &val in vals.iter()
    {
      graph.add_node(val).unwrap();
    }
    // values that have been added have the correct index
    for (itr,&val) in vals.iter().enumerate()
    {
      let res: Option<usize>=graph.get_idx(val);
      assert!(res.is_some());
      assert!(res.unwrap()==itr);
    }
    // a value that hasn't been added has no index
    let res: Option<usize>=graph.get_idx(2.93);
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

    // test error when trying to connect already is_connected Nodes
    let res: Result<Rc<RefCell<Edge<i32>>>,i32>=graph.connect(173,-98);
    assert!(res.is_err());
    // the Err Result should be the first value
    match res
    {
      Err(x) => assert!(x==173),
      _      => (),
    }
    assert!(graph.edges.len()==2);
    // and the other way around
    let res: Result<Rc<RefCell<Edge<i32>>>,i32>=graph.connect(-98,173);
    assert!(res.is_err());
    // the Err Result should be the first value
    match res
    {
      Err(x) => assert!(x==173),
      _      => (),
    }
    assert!(graph.edges.len()==2);
  }

  #[test]
  fn test_iter()
  {
    let mut gr: Graph<char>=Graph::<char>::new();
    let vals: [char;4]=['a','b','c','z'];
    
    for val in vals.into_iter()
    {
      gr.add_node(*val).unwrap();
    }

    let mut itr: usize=0;
    for nd in gr.into_iter()
    {
      assert!(nd.borrow().val==vals[itr]);
      itr+=1;
    }
    // (compile time?) test that the iter doesn't move the Graph
    gr.add_node('y').unwrap();
  }

  #[test]
  fn test_is_empty()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    assert!(gr.is_empty());
    gr.add_node(3.14).unwrap();
    assert!(!gr.is_empty());
  }

  #[test]
  fn test_is_trivial()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    assert!(!gr.is_trivial());

    gr.add_node(3.14).unwrap();
    assert!(gr.is_trivial());

    gr.add_node(1.618).unwrap();
    assert!(!gr.is_trivial());
  }

  #[test]
  fn test_is_edgeless()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    assert!(gr.is_edgeless());
    gr.add_node(3.14).unwrap();
    assert!(gr.is_edgeless());
    gr.add_node(1.618).unwrap();
    assert!(gr.is_edgeless());
    gr.add_node(2.718).unwrap();
    assert!(gr.is_edgeless());
    gr.add_node(-0.083).unwrap();
    assert!(gr.is_edgeless());
    
    gr.connect(3.14,2.718).unwrap();
    assert!(!gr.is_edgeless());
    gr.connect(3.14,1.618).unwrap();
    assert!(!gr.is_edgeless());
  }

  #[test]
  fn test_order()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    assert!(gr.order()==0);

    gr.add_node(3.14).unwrap();
    assert!(gr.order()==1);

    gr.add_node(1.618).unwrap();
    assert!(gr.order()==2);
    
    gr.connect(3.14,1.618).unwrap();
    assert!(gr.order()==2);
  }

  #[test]
  fn test_size()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    assert!(gr.size()==0);
    gr.add_node(3.14).unwrap();
    assert!(gr.size()==0);
    gr.add_node(1.618).unwrap();
    assert!(gr.size()==0);
    gr.add_node(2.718).unwrap();
    assert!(gr.size()==0);
    gr.add_node(-0.083).unwrap();
    assert!(gr.size()==0);
    
    gr.connect(3.14,2.718).unwrap();
    assert!(gr.size()==1);

    gr.connect(3.14,1.618).unwrap();
    assert!(gr.size()==2);

    gr.connect(1.618,-0.083).unwrap();
    assert!(gr.size()==3);
  }

  #[test]
  fn test_is_connected()
  {
    let mut gr: Graph<i32>=Graph::<i32>::new();
    assert!(!gr.is_connected());
    gr.add_node(10858);
    assert!(!gr.is_connected());
    gr.add_node(8191);
    assert!(!gr.is_connected());
    gr.connect(10858,8191);
    assert!(gr.is_connected());
    gr.add_node(78557);
    assert!(!gr.is_connected());
    gr.connect(78557,10858);
    assert!(gr.is_connected());
    gr.add_node(6);
    gr.connect(78557,8191);
    assert!(!gr.is_connected());
    gr.connect(10858,6);
    assert!(gr.is_connected());
    gr.add_node(1729);
    assert!(!gr.is_connected());
    gr.add_node(30357);
    assert!(!gr.is_connected());
    gr.connect(1729,30357);
    assert!(!gr.is_connected());
  }

  #[test]
  fn test_hamiltonian_path()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    gr.add_node(3.14);
    gr.add_node(1.618);
    gr.add_node(2.718);
    gr.add_node(-0.083);
    assert!(gr.hamiltonian_path().is_none());
    gr.connect(3.14,1.618);
    gr.connect(-0.083,1.618);
    gr.connect(2.718,1.618);
    assert!(gr.hamiltonian_path().is_none());
    gr.connect(2.718,-0.083);
    assert!(gr.hamiltonian_path().is_some());
  }
}
