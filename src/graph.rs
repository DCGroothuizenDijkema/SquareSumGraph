
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

struct Node<'a,T>
  where T: Scalar
{
}

struct Edge<'a,T>
  where T: Scalar
{
}

pub struct Graph<'a,T>
  where T: Scalar
{
  nodes: std::vec::Vec<Node<'a,T>>,
  edges: std::vec::Vec<Edge<'a,T>>,
}
