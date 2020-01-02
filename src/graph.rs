
struct Node<T>
{
  val: T,
}

struct Edge
{
}

pub struct Graph<T>
{
  nodes: std::vec::Vec<Node<T>>,
  edges: std::vec::Vec<Edge>,
}
