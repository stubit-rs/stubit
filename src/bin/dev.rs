use stubit::Bits;

fn main() {
    let mut bits = Bits::new();
    for _ in 0..130 {
        bits.push(1);
    }

    for i in bits.repr() {
        println!("{:064b}", i);
    }
}
