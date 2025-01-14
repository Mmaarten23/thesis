use std::cell::{UnsafeCell, Cell};
use std::fmt;

// Our minimal RefCell implementation
pub struct MyRefCell<T> {
    value: UnsafeCell<T>,     // Allows interior mutability
    borrow_count: Cell<i32>,  // Tracks the number of active immutable borrows
    mutable_borrowed: Cell<bool>, // Tracks if a mutable borrow is active
}

impl<T> MyRefCell<T> {
    // Constructor for MyRefCell
    pub fn new(value: T) -> MyRefCell<T> {
        MyRefCell {
            value: UnsafeCell::new(value),
            borrow_count: Cell::new(0),
            mutable_borrowed: Cell::new(false),
        }
    }

    // Immutable borrow
    pub fn borrow(&self) -> MyRef<'_, T> {
        if self.mutable_borrowed.get() {
            panic!("Already mutably borrowed!");
        }
        self.borrow_count.set(self.borrow_count.get() + 1);
        MyRef { refcell: self }
    }

    // Mutable borrow
    pub fn borrow_mut(&self) -> MyRefMut<'_, T> {
        if self.borrow_count.get() > 0 || self.mutable_borrowed.get() {
            panic!("Already borrowed!");
        }
        self.mutable_borrowed.set(true);
        MyRefMut { refcell: self }
    }
}

// Drop implementations to decrement the borrow count when a reference goes out of scope
impl<T> Drop for MyRefCell<T> {
    fn drop(&mut self) {
        // We could add debug checks here to ensure no borrows are active on drop.
    }
}

// Struct to represent an immutable borrow
pub struct MyRef<'a, T> {
    refcell: &'a MyRefCell<T>,
}

impl<'a, T> Drop for MyRef<'a, T> {
    fn drop(&mut self) {
        self.refcell.borrow_count.set(self.refcell.borrow_count.get() - 1);
    }
}

impl<'a, T> std::ops::Deref for MyRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safe because borrow() checks borrowing rules
        unsafe { &*self.refcell.value.get() }
    }
}

// Struct to represent a mutable borrow
pub struct MyRefMut<'a, T> {
    refcell: &'a MyRefCell<T>,
}

impl<'a, T> Drop for MyRefMut<'a, T> {
    fn drop(&mut self) {
        self.refcell.mutable_borrowed.set(false);
    }
}

impl<'a, T> std::ops::Deref for MyRefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safe because borrow_mut() checks borrowing rules
        unsafe { &*self.refcell.value.get() }
    }
}

impl<'a, T> std::ops::DerefMut for MyRefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        // Safe because borrow_mut() checks borrowing rules
        unsafe { &mut *self.refcell.value.get() }
    }
}

// Optional: Implement Debug trait for nicer printing
impl<T: fmt::Debug> fmt::Debug for MyRefCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MyRefCell")
            .field("value", unsafe { &*self.value.get() })
            .finish()
    }
}
