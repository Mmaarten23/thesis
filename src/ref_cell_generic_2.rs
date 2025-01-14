// verifast_options{ignore_ref_creation}

use std::cell::UnsafeCell;
use std::process;

/*
 * MinimalRefCell is a simplified version of RefCell from the standard library
 * that supports only mutable borrows (borrow_mut), using only UnsafeCell.
 */
pub struct MinimalRefCell<T> {
    value: UnsafeCell<T>,          // The value being stored. Mutable even when the RefCell is immutable.
    mutable_borrowed: UnsafeCell<bool>, // Tracks whether a mutable borrow is active, using UnsafeCell for interior mutability.
}

/*@
lem MinimalRefCell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *_)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]MinimalRefCell_share::<T>(k, t, l);
    ens type_interp::<T>() &*& [_]MinimalRefCell_share::<T>(k1, t, l);
{
    assume(false);
}

lem MinimalRefCell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *_)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& full_borrow(k, MinimalRefCell_full_borrow_content::<T>(t, l)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [_]MinimalRefCell_share::<T>(k, t, l) &*& [q]lifetime_token(k);
{
    assume(false);
}

lem init_ref_MinimalRefCell<T>(p: *MinimalRefCell<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]MinimalRefCell_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]MinimalRefCell_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

lem MinimalRefCell_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Send(typeid(T)) == true &*& MinimalRefCell_own::<T>(?t0, ?v);
    ens type_interp::<T>() &*& MinimalRefCell_own::<T>(t1, v);
{
    assume(false);
}

    pred<T> <MinimalRefCell<T>>.own(t, cell) = <T>.own(t, cell.value) &*& bool_own(t, cell.mutable_borrowed);
@*/
 
/*@

fix Narc() -> *u8 { 42 as *u8 }
fix Marc() -> mask_t { MaskSingle(Narc) }

pred_ctor dlft_pred(dk: lifetime_t)(gid: isize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };

pred_ctor ticket_(dk: lifetime_t, gid: isize, frac: real)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]ghost_cell(gid, false);

pred_ctor MinimalRefCell_inv<T>(dk: lifetime_t, ptr: *MinimalRefCell<T>, gid: isize)() =
    counting(dlft_pred(dk), gid, ?n, ?destroyed) &*&
    if n <= 0 { true }
    else { 
        (*ptr).mutable_borrowed |-> ?borrowed &*&
        (*ptr).value |-> ?val
    };

pred<T> <MinimalRefCell<T>>.share(k, t, l) =
    [_]exists(?ptr) &*&
    l == ptr &*&

    [_]exists(?gid) &*& [_]exists(?dk) &*& 

    [_]atomic_space(Marc, MinimalRefCell_inv(dk, ptr, gid)) &*&
    
    [_]exists(?frac) &*&
    [_]frac_borrow(k, ticket_(dk, gid, frac)) &*&
    [_]frac_borrow(k, lifetime_token_(frac, dk)) &*&
    
    [_](<T>.share)(dk, default_tid, &(*ptr).value) &*&
    (*l).mutable_borrowed |-> ?borrowed;
    // &*&

    
    // Ensures the value pointer is valid and within memory limits.
    //pointer_within_limits(&(*ptr).value) == true &*&
    //pointer_within_limits(&(*ptr).mutable_borrowed) == true;
@*/



impl<T> MinimalRefCell<T> {
    pub fn new(value: T) -> Self {
        let r = MinimalRefCell {
        	value: UnsafeCell::new(value), 
        	mutable_borrowed: UnsafeCell::new(false)
        };
        //@ close MinimalRefCell_own::<T>(_t, r);
        r
    }

    pub fn borrow_mut<'a>(this: &'a Self) -> MinimalRefMut<'a, T> {
        //@ open MinimalRefCell_share::<T>()('a, _t, this);
        unsafe {
            if *this.mutable_borrowed.get() == false {
            // open atomic_space(Marc, MinimalRefCell_inv(_t, dk, ptr, gid));
                *this.mutable_borrowed.get() = true;
            } else {
                process::abort();
            }
        }
        // Return a MinimalRefMut object that will reset the mutable_borrowed flag when dropped
        MinimalRefMut { refcell: this }
    }
}

impl<T> Drop for MinimalRefCell<T> {
    // When the RefCell is dropped, check if it is still mutably borrowed.
    // If it is, abort.
    fn drop(&mut self) {
        unsafe {
            if *self.mutable_borrowed.get() {
                process::abort();
            }
        }
    }
}

// Struct to represent a mutable borrow
pub struct MinimalRefMut<'a, T: 'a> {
    refcell: &'a MinimalRefCell<T>,
}

// When dropped, reset the mutable_borrowed flag
impl<'a, T> Drop for MinimalRefMut<'a, T> {
    fn drop(&mut self) {
        unsafe {
            *self.refcell.mutable_borrowed.get() = false;
        }
    }
}

// Allow accessing the value through the mutable reference with a direct dereference
impl<'a, T> std::ops::DerefMut for MinimalRefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        // Safe because borrow_mut() checks borrowing rules
        unsafe { &mut *self.refcell.value.get() }
    }
}

// Ignore Deref for now by making it abort
impl<'a, T> std::ops::Deref for MinimalRefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // As suggested, abort to simplify VeriFast verification
        process::abort();
    }
}