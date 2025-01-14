use std::cell::{UnsafeCell, Cell};

/*
 * MinimalRefCell is a simplified version of RefCell from the standard library 
 * that serves as a warm-up exercise.
 */
pub struct MinimalRefCell<T> {
    value: UnsafeCell<T>, // The value being stored. Mutable even when the RefCell is immutable.
    immutable_borrow_count: Cell<i32>, // Tracks the number of active immutable borrows
    mutable_borrowed: Cell<bool>, // Tracks whether a mutable borrow is active
}

impl<T> MinimalRefCell<T> {
    pub fn new(value: T) -> MinimalRefCell<T> {
        MinimalRefCell {
            value: UnsafeCell::new(value), // Initialize the value with the provided value
            immutable_borrow_count: Cell::new(0), // No active borrows initially
            mutable_borrowed: Cell::new(false), // No active mutable borrows initially
        }
    }

    // Immutable borrow
    pub fn borrow(&self) -> MinimalRef<'_, T> {
        if self.mutable_borrowed.get() {
            // If the RefCell is already mutably borrowed, panic
            // Immutable borrows can coexist, but mutable borrows cannot
            panic!("RefCell already mutably borrowed!");
        }
        self.immutable_borrow_count.set(self.immutable_borrow_count.get() + 1); // Increment borrow count
        MinimalRef { refcell: self } // Return a MinimalRef object that will decrement the borrow count when dropped (See Drop trait implementation)
    }

    // Mutable borrow
    pub fn borrow_mut(&self) -> MinimalRefMut<'_, T> {
        if self.immutable_borrow_count.get() > 0 || self.mutable_borrowed.get() {
            // If the RefCell is already borrowed, panic
            // Doesn't matter if the borrow is mutable or immutable
            panic!("RefCell already borrowed (im)mutably!");
        }
        self.mutable_borrowed.set(true); // Indicate that the RefCell is mutably borrowed
        MinimalRefMut { refcell: self } // Return a MinimalRefMut object that will reset the mutable_borrowed flag when dropped (See Drop trait implementation)
    }
}

impl<T> Drop for MinimalRefCell<T> {
    // When the RefCell is dropped, check if there are any active borrows
    // If there are... something went wrong in the borrow tracking logic. Panic.
    fn drop(&mut self) {
        // Debug check: No active borrows should exist when the RefCell is being dropped
        if self.immutable_borrow_count.get() != 0 {
            panic!("MinimalRefCell dropped while there are active immutable borrows!");
        }
        if self.mutable_borrowed.get() {
            panic!("MinimalRefCell dropped while it is mutably borrowed!");
        }
    }
}

// Struct to represent an immutable borrow
pub struct MinimalRef<'a, T: 'a> {
    refcell: &'a MinimalRefCell<T>,
}

// When dropped, decrement the borrow count
// Reference went out of scope, so the borrow is no longer active
impl<'a, T> Drop for MinimalRef<'a, T> {
    fn drop(&mut self) {
        self.refcell.immutable_borrow_count.set(self.refcell.immutable_borrow_count.get() - 1); // Decrement borrow count when ref is dropped
    }
}

// Allow accessing the value through the reference with a direct dereference
impl<'a, T> std::ops::Deref for MinimalRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // Safe because borrow() checks borrowing rules
        // At the point of dereferencing, we know that the borrow is valid.
        unsafe { &*self.refcell.value.get() }
    }
}

// Struct to represent a mutable borrow
pub struct MinimalRefMut<'a, T: 'a> {
    refcell: &'a MinimalRefCell<T>,
}

// When dropped, reset the mutable_borrowed flag
// Reference went out of scope, so the mutable borrow is no longer active
impl<'a, T> Drop for MinimalRefMut<'a, T> {
    fn drop(&mut self) {
        self.refcell.mutable_borrowed.set(false);
    }
}

// Allow accessing the value through the mutable reference with a direct dereference
impl<'a, T> std::ops::Deref for MinimalRefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // Safe because borrow_mut() checks borrowing rules
        // At the point of dereferencing, we know that the borrow is valid.
        unsafe { &*self.refcell.value.get() }
    }
}

impl<'a, T> std::ops::DerefMut for MinimalRefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        // Safe because borrow_mut() checks borrowing rules
        unsafe { &mut *self.refcell.value.get() }
    }
}