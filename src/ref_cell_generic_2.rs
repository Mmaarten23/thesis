// verifast_options{ignore_ref_creation}

use std::cell::UnsafeCell;
use std::process;

/*
 * MinimalRefCell is a simplified version of RefCell from the standard library
 * that supports only mutable borrows (borrow_mut), using only UnsafeCell.
 */
pub struct MinimalRefCell<T> {
    value: UnsafeCell<T>, // The value being stored. Mutable even when the RefCell is immutable.
    mutable_borrowed: UnsafeCell<bool>, // Tracks whether a mutable borrow is active, using UnsafeCell for interior mutability.
}

/*@
pred True(;) = true;
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
pred<T> <MinimalRefCell<T>>.own(t, cell) = <T>.own(t, cell.value);

pred_ctor nonatomic_borrow_content<T>(ptr: *MinimalRefCell<T>, t: thread_id_t, k: lifetime_t)() =
    MinimalRefCell_mutable_borrowed(ptr, ?borrowed) &*&
    pointer_within_limits(&(*ptr).mutable_borrowed) == true &*&
    pointer_within_limits(&(*ptr).value) == true &*&
    if borrowed { true }
    else {
        full_borrow(k, <T>.full_borrow_content(t, &(*ptr).value))
    };

pred<T> <MinimalRefCell<T>>.share(k, t, l) =
    exists(?dk) &*&
    lifetime_inclusion(k, dk) == true &*&
    [_]nonatomic_borrow(k, t, MaskNshrSingle(l), nonatomic_borrow_content(l, t, dk));


lem MinimalRefCell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *MinimalRefCell<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]MinimalRefCell_share::<T>(k, t, l);
    ens type_interp::<T>() &*& [_]MinimalRefCell_share::<T>(k1, t, l);
{
    open [?df]MinimalRefCell_share::<T>(k, t, l);
    assert [_]nonatomic_borrow(k, t, ?m, _) &*& [_]exists(?dk);
    nonatomic_borrow_mono(k, k1, t, m, nonatomic_borrow_content(l, t, dk));
    lifetime_inclusion_trans(k1, k, dk);
    close [df]MinimalRefCell_share::<T>(k1, t, l);
}
pred_ctor MinimalRefCell_padding<T>(l: *MinimalRefCell<T>)(;) = struct_MinimalRefCell_padding(l);

lem MinimalRefCell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *MinimalRefCell<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& full_borrow(k, MinimalRefCell_full_borrow_content::<T>(t, l)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [_]MinimalRefCell_share::<T>(k, t, l) &*& [q]lifetime_token(k);
{
    produce_lem_ptr_chunk implies(MinimalRefCell_full_borrow_content(t, l), sep(MinimalRefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed))))() {
        open MinimalRefCell_full_borrow_content::<T>(t, l)();
        assert (*l).value |-> ?value &*& (*l).mutable_borrowed |-> ?mutable_borrowed;
        open MinimalRefCell_own::<T>()(t, MinimalRefCell::<T> { value, mutable_borrowed });

        close_full_borrow_content::<T>(t, &(*l).value);
        close bool_full_borrow_content(t, &(*l).mutable_borrowed)();
        close sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed))();
        close MinimalRefCell_padding::<T>(l)();
        close sep(MinimalRefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed)))();
    } {
        produce_lem_ptr_chunk implies(sep(MinimalRefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed))), MinimalRefCell_full_borrow_content(t, l))() {
            open sep(MinimalRefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed)))();
            open MinimalRefCell_padding::<T>(l)();
            open sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed))();
            open_full_borrow_content::<T>(t, &(*l).value);
            open bool_full_borrow_content(t, &(*l).mutable_borrowed)();
            assert (*l).value |-> ?value &*& (*l).mutable_borrowed |-> ?mutable_borrowed;
            close MinimalRefCell_own::<T>(t, MinimalRefCell::<T> { value: value, mutable_borrowed: mutable_borrowed });
            close MinimalRefCell_full_borrow_content::<T>(t, l)();
        } {
            full_borrow_implies(k, MinimalRefCell_full_borrow_content(t, l), sep(MinimalRefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed))));
        }
    }
    full_borrow_split_m(k, MinimalRefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed)));
    full_borrow_split_m(k, <T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutable_borrowed)); // LFTL-BOR-SPLIT
    open_full_borrow_m(q, k, <T>.full_borrow_content(t, &(*l).value));
    open_full_borrow_content(t, &(*l).value);
    points_to_limits(&(*l).value);
    close_full_borrow_content(t, &(*l).value);
    close_full_borrow_m(<T>.full_borrow_content(t, &(*l).value));


    let kstrong = open_full_borrow_strong_m(k, bool_full_borrow_content(t, &(*l).mutable_borrowed), q); // LFTL-BOR-ACC-STRONG
    produce_lem_ptr_chunk full_borrow_convert_strong(True, nonatomic_borrow_content(l, t, k), kstrong, bool_full_borrow_content(t, &(*l).mutable_borrowed))() {
        open nonatomic_borrow_content::<T>(l, t, k)();
        if (*l).mutable_borrowed == false {
            leak full_borrow(_, <T>.full_borrow_content(t, &(*l).value));
        }
        close bool_full_borrow_content(t, &(*l).mutable_borrowed)();
    }{
        open bool_full_borrow_content(t, &(*l).mutable_borrowed)();
        close exists(k);

        if (*l).mutable_borrowed == true {
            leak full_borrow(_, <T>.full_borrow_content(t, &(*l).value));
        }
        points_to_limits(&(*l).mutable_borrowed);
        close nonatomic_borrow_content::<T>(l, t, k)();
        close_full_borrow_strong_m(kstrong, bool_full_borrow_content(t, &(*l).mutable_borrowed), nonatomic_borrow_content(l, t, k));
        full_borrow_into_nonatomic_borrow_m(kstrong, t, MaskNshrSingle(l), nonatomic_borrow_content(l, t, k));
        nonatomic_borrow_mono(kstrong, k, t, MaskNshrSingle(l), nonatomic_borrow_content(l, t, k));
        close exists(k);
        close MinimalRefCell_share::<T>(k, t, l);
        leak MinimalRefCell_share::<T>(k, t, l);
        leak full_borrow(k, MinimalRefCell_padding(l));
    }
}
@*/

impl<T> MinimalRefCell<T> {
    pub fn new(value: T) -> Self {
        let r = MinimalRefCell {
            value: UnsafeCell::new(value),
            mutable_borrowed: UnsafeCell::new(false),
        };
        //@ close MinimalRefCell_own::<T>(_t, r);
        r
    }

    pub fn borrow_mut<'a>(this: &'a Self) -> MinimalRefMut<'a, T> {
        //@ open MinimalRefCell_share::<T>()('a, _t, this);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?dk);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, nonatomic_borrow_content(this, _t, dk));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open nonatomic_borrow_content::<T>(this, _t, dk)();
            if *this.mutable_borrowed.get() == false {
                *this.mutable_borrowed.get() = true;
            } else {
                process::abort();
            }
        }
        //@ assert partial_thread_token(_t, ?mask0);
        //@ close nonatomic_borrow_content::<T>(this, _t, dk)();
        //@ close_nonatomic_borrow();
        //@ thread_token_merge(_t, mask0, mask);
        //@ close thread_token(_t);
        // Return a MinimalRefMut object that will reset the mutable_borrowed flag when dropped
        //@ assert full_borrow(?kv, <T>.full_borrow_content(_t, &(*this).value));
        //@ close exists(kv);
        let r = MinimalRefMut { refcell: this };
        //@ close MinimalRefMut_own::<'a, T>(_t, r);
        r
    }
}

impl<T> Drop for MinimalRefCell<T> {
    // When the RefCell is dropped, check if it is still mutably borrowed.
    // If it is, abort.
    fn drop(&mut self) {
        //@ open MinimalRefCell_full_borrow_content::<T>(_t, self)();
        //@ open MinimalRefCell_own::<T>(_t, ?s);
        unsafe {
            if *self.mutable_borrowed.get() {
                process::abort();
            }
        }
    }
}

/*@

pred<'a, T> <MinimalRefMut<'a, T>>.own(t, cell) =
    [_]exists(?dk) &*&
    lifetime_inclusion('a, dk) == true &*&
    pointer_within_limits(&(*cell.refcell).value) == true &*&
    full_borrow(dk, <T>.full_borrow_content(t, &(*cell.refcell).value)) &*&
    [_]nonatomic_borrow('a, t, MaskNshrSingle(cell.refcell), nonatomic_borrow_content::<T>(cell.refcell, t, dk));
@*/
// Struct to represent a mutable borrow
pub struct MinimalRefMut<'a, T> {
    refcell: &'a MinimalRefCell<T>,
}

/*@

lem MinimalRefMut_own_mono<'a0, 'a1, T>()
    req type_interp::<T>() &*& MinimalRefMut_own::<'a0, T>(?t, ?v) &*& lifetime_inclusion('a1, 'a0) == true;
    ens type_interp::<T>() &*& MinimalRefMut_own::<'a1, T>(t, MinimalRefMut::<'a1, T> { refcell: v.refcell as *_ });
{
    assume(false);
}

lem MinimalRefMut_send<'a, T>(t1: thread_id_t)
    req type_interp::<T>() &*& MinimalRefMut_own::<'a, T>(?t0, ?v);
    ens type_interp::<T>() &*& MinimalRefMut_own::<'a, T>(t1, v);
{
    assume(false);
}

@*/

// When dropped, reset the mutable_borrowed flag
impl<'a, T> Drop for MinimalRefMut<'a, T> {
    fn drop(&mut self) {
        //@ open MinimalRefMut_full_borrow_content::<'a, T>(_t, self)();
        //@ open MinimalRefMut_own::<'a, T>(_t, ?s);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?dk);
            //@ assert MinimalRefMut_refcell::<'a, T>(self, ?cell);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, nonatomic_borrow_content(cell, _t, dk));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open nonatomic_borrow_content::<T>(cell, _t, dk)();
            /*@ if !(*(*self).refcell).mutable_borrowed {
                leak full_borrow(dk, _);
            }
            @*/
            *self.refcell.mutable_borrowed.get() = false;
            //@ assert partial_thread_token(_t, ?mask0);
            //@ close nonatomic_borrow_content::<T>(cell, _t, dk)();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask0, mask);
            //@ close thread_token(_t);
            //@ close exists(dk);
            //@ close MinimalRefCell_share::<T>('a, _t, cell);
            //@ leak MinimalRefCell_share::<T>('a, _t, cell);
           
        }
    }
}

// Allow accessing the value through the mutable reference with a direct dereference
impl<'a, T> std::ops::DerefMut for MinimalRefMut<'a, T> {
    fn deref_mut<'b>(&'b mut self) -> &'b mut T {
        // Safe because borrow_mut() checks borrowing rules
        unsafe {
            //@ assert [?qb]lifetime_token('b);
            //@ open_full_borrow(qb, 'b, MinimalRefMut_full_borrow_content::<'a, T>(_t, self));
            //@ open MinimalRefMut_full_borrow_content::<'a, T>(_t, self)();
            //@ open MinimalRefMut_own::<'a, T>(_t, *self);
            //@ assert [_]exists(?dk);
            //@ lifetime_token_trade('a, _q_a, dk);
            //@ assert [?qdk]lifetime_token(dk);
            //@ open_full_borrow(qdk, dk, <T>.full_borrow_content(_t, &(*(*self).refcell).value));
            //@ open_full_borrow_content::<T>(_t, &(*(*self).refcell).value);
            let r = &mut *self.refcell.value.get();
            //@ close_full_borrow_content::<T>(_t, &(*(*self).refcell).value);
            //@ close_full_borrow(<T>.full_borrow_content(_t, &(*(*self).refcell).value));
            //@ lifetime_token_trade_back(qdk, dk);
            //@ close MinimalRefMut_own::<'a, T>(_t, *self);
            //@ close MinimalRefMut_full_borrow_content::<'a, T>(_t, self)();
            //@ close_full_borrow(MinimalRefMut_full_borrow_content::<'a, T>(_t, self));
            r
        }
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


