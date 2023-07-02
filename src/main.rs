mod gvec;
use gvec::*;
mod gen;
use gen::*;

fn main() {
    let mut data: GVec<&str> = gvec![];

    let foo: GIdx = data.insert("foo");
    let bar = data.insert("bar");

    assert_eq!(data[foo], "foo");
    assert_eq!(data[bar], "bar");

    assert_eq!(data.get(foo), Some(&"foo"));
    assert_eq!(data.remove(foo), Some("foo"));
    assert_eq!(data.get(foo), None);

    let baz = data.insert("baz");

    assert_eq!(baz.idx, foo.idx);
    assert_eq!(data.get(foo), None);
    assert_eq!(data.get(baz), Some(&"baz"));

    let (mut chars, [a, b, c]) = gvec!['a', 'b', 'c'];
}

















