use crate::ref_cell_generic::MinimalRefCell;

mod ref_cell_generic;
mod ref_cell_u32;
mod ref_cell_generic_2;

fn main() {
    let cell = MinimalRefCell::new(42);

    {
        let val1 = cell.borrow();
        let val2 = cell.borrow();
        println!("Val1: {}", *val1);
        println!("Val2: {}", *val2);
    } // val1 and val2 are dropped here, so borrow_count is decremented

    {
        let mut val = cell.borrow_mut();
        *val += 1;
        println!("Mutated Val: {}", *val);
    } // val is dropped here, so mutable_borrowed is reset
}