
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//
//                                                                                                                                       //
// graph.rs                                                                                                                              //
//                                                                                                                                       //
// D. C. Groothuizen Dijkema - January, 2020                                                                                             //
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//

// Graph theory related classes, traits, and impls


#![allow(dead_code)]

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

struct Node<T>
  where T: Scalar
{
  val: T,
  edges: std::vec::Vec<std::rc::Rc<Edge<T>>>,
}

impl<T> Node<T>
  where T: Scalar
{
  fn new(val: T) -> Self
  {
    Node{val:val,edges:std::vec::Vec::<std::rc::Rc<Edge<T>>>::new()}
  }
}

struct Edge<T>
  where T: Scalar
{
  nodes: std::vec::Vec<std::rc::Rc<Node<T>>>,
}

pub struct Graph<T>
  where T: Scalar
{
  nodes: std::vec::Vec<std::rc::Rc<Node<T>>>,
  edges: std::vec::Vec<std::rc::Rc<Edge<T>>>,
}

impl<T> Graph<T>
  where T: Scalar
{
  fn new() -> Self
  {
    Graph{nodes:std::vec::Vec::<std::rc::Rc<Node<T>>>::new(),edges:std::vec::Vec::<std::rc::Rc<Edge<T>>>::new()}
  }

  fn add_node(&mut self,val: T) -> std::result::Result<std::rc::Rc<Node<T>>,usize>
  {
    for node in &self.nodes
    {
      if node.val==val { return std::result::Result::Err(1); }
    }
    let nd: std::rc::Rc<Node<T>>=std::rc::Rc::new(Node::new(val));
    let res: std::result::Result<std::rc::Rc<Node<T>>,usize>=std::result::Result::Ok(std::rc::Rc::clone(&nd));

    self.nodes.push(nd);
    res
  }

  fn connect(&mut self,val_one: T,val_two: T) -> std::result::Result<std::rc::Rc<Edge<T>>,T>
  {
    let node_one: std::option::Option<std::rc::Rc<Node<T>>>=self.find(val_one);
    let node_two: std::option::Option<std::rc::Rc<Node<T>>>=self.find(val_two);

    if node_one.is_none() { return std::result::Result::Err(val_one); }
    if node_two.is_none() { return std::result::Result::Err(val_two); }

    let node_one: std::rc::Rc<Node<T>>=node_one.unwrap();
    let node_two: std::rc::Rc<Node<T>>=node_two.unwrap();

    let edge: std::rc::Rc<Edge<T>>=std::rc::Rc::new(Edge{nodes:vec![std::rc::Rc::clone(&node_one),std::rc::Rc::clone(&node_two)]});
    let res: std::result::Result<std::rc::Rc<Edge<T>>,T>=std::result::Result::Ok(std::rc::Rc::clone(&edge));
    
    self.edges.push(edge);
    res
  }

  fn find(&self,val: T) -> std::option::Option<std::rc::Rc<Node<T>>>
  {
    for node in &self.nodes
    {
      if node.val==val { return std::option::Option::Some(std::rc::Rc::clone(&node)); }
    }
    std::option::Option::None
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
    let res: std::result::Result<std::rc::Rc<Node<usize>>,usize>=graph.add_node(2);
    assert!(res.is_ok());
    match res
    {
      Ok(x) => assert!(x.val==2),
      _     => (),
    }
    assert!(graph.nodes[0].val==2);
    assert!(graph.nodes.len()==1);
    
    // test an invalid insertion
    let res: std::result::Result<std::rc::Rc<Node<usize>>,usize>=graph.add_node(2);
    assert!(res.is_err());
    match res
    {
      Err(x) => assert!(x==1),
      _     => (),
    }
    assert!(graph.nodes.len()==1);

    // test another valid insertion
    let res: std::result::Result<std::rc::Rc<Node<usize>>,usize>=graph.add_node(1729);
    assert!(res.is_ok());
    match res
    {
      Ok(x) => assert!(x.val==1729),
      _     => (),
    }
    assert!(graph.nodes.len()==2);
    assert!(graph.nodes[1].val==1729);
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
      let res: std::option::Option<std::rc::Rc<Node<f64>>>=graph.find(val);
      assert!(res.is_some());
      let nd: std::rc::Rc<Node<f64>>=res.unwrap();
      assert!(nd.val==val);
    }
    // a value that hasn't been added cannot be found
    let res: std::option::Option<std::rc::Rc<Node<f64>>>=graph.find(2.93);
    assert!(res.is_none());
  }

  #[test]
  fn test_connect()
  {
    // test error
    let mut graph=Graph::<i32>::new();
    let res: std::result::Result<std::rc::Rc<Edge<i32>>,i32>=graph.connect(173,-98);
    assert!(res.is_err());
    match res
    {
      Err(x) => assert!(x==173),
      _      => (),
    }
    assert!(graph.edges.is_empty());

    let nd_one: std::rc::Rc<Node<i32>>=graph.add_node(173).unwrap();
    let res: std::result::Result<std::rc::Rc<Edge<i32>>,i32>=graph.connect(173,-98);
    assert!(res.is_err());
    match res
    {
      Err(x) => assert!(x==-98),
      _      => (),
    }
    assert!(graph.edges.is_empty());

    let nd_two: std::rc::Rc<Node<i32>>=graph.add_node(-98).unwrap();
    let res: std::result::Result<std::rc::Rc<Edge<i32>>,i32>=graph.connect(173,-98);
    assert!(graph.edges.len()==1);
    assert!(res.is_ok());
    let edge: std::rc::Rc<Edge<i32>>=res.unwrap();
    assert!(&*nd_one as *const Node<i32> == &*edge.nodes[0] as *const Node<i32>);
    assert!(&*nd_two as *const Node<i32> == &*edge.nodes[1] as *const Node<i32>);

    let nd_three: std::rc::Rc<Node<i32>>=graph.add_node(1).unwrap();
    let res: std::result::Result<std::rc::Rc<Edge<i32>>,i32>=graph.connect(173,1);
    assert!(graph.edges.len()==2);
    assert!(res.is_ok());
    let edge: std::rc::Rc<Edge<i32>>=res.unwrap();
    assert!(&*nd_one as *const Node<i32> == &*edge.nodes[0] as *const Node<i32>);
    assert!(&*nd_three as *const Node<i32> == &*edge.nodes[1] as *const Node<i32>);

    assert!(&*graph.nodes[0] as *const Node<i32> == &*graph.edges[0].nodes[0] as *const Node<i32>);
    assert!(&*graph.nodes[0] as *const Node<i32> == &*graph.edges[1].nodes[0] as *const Node<i32>);
    assert!(&*graph.nodes[1] as *const Node<i32> == &*graph.edges[0].nodes[1] as *const Node<i32>);
    assert!(&*graph.nodes[2] as *const Node<i32> == &*graph.edges[1].nodes[1] as *const Node<i32>);
  }
}