mod ref_cell;

fn main() {
    let z: isize = 5;
    let x: isize = 4;
    println!("{}", z);
    println!("{}", x);
    println!("{:?}", z.checked_sub(x));
    println!("{:?}", x.checked_sub(z));
}