use std::{ops::{Sub, Add, Deref, DerefMut}, borrow::{Borrow, BorrowMut}, marker::PhantomData, cell::UnsafeCell, process::Output};

pub struct Counted<T, R>
where R: RefCounter {
    refs: UnsafeCell<R>,
    val: UnsafeCell<T>
}

pub struct Ref<'a, T, R>
where R: RefCounter {
    counted: &'a Counted<T, R>
}

pub struct Mut<'a, T, R>
where R: RefCounter {
    counted: &'a Counted<T, R>
}

impl<'a, T, R> Counted<T, R>
where R: RefCounter {

    pub fn new(val: T, mut refs: R) -> Self {
        unsafe { refs.set_refs(R::NO_REFS) };
        Self { refs: UnsafeCell::new(refs), val: UnsafeCell::new(val)}
    }

    /// Bypass safety checks to get a mutable reference to the inner `refs` field
    pub unsafe fn refs(&'a self) -> &'a mut R {
        &mut *self.refs.get()
    }

    /// Bypass safety checks to get a mutable reference to the inner `val` field
    pub unsafe fn val(&'a self) -> &'a mut T {
        &mut *self.val.get()
    }
}

/// Trait containing all the operations a reference counter needs
/// 
/// This can be implemented on any type by providing values for the necessary constants
/// that follow the safety rules below
/// 
/// The typical implementation follows these steps:
/// - [RefCounter::LITERAL_ONE] is the representation of numeric `1` for the type, not necessarily the value for one reference
/// - [RefCounter::MUT_FROZEN] is the largest valid value
/// - [RefCounter::MUT_ACTIVE] = [RefCounter::MUT_FROZEN] - [RefCounter::LITERAL_ONE]
/// - [RefCounter::MAX_IMMUT] = [RefCounter::MUT_ACTIVE] - [RefCounter::LITERAL_ONE]
/// - [RefCounter::NO_REFS] is the smallest valid value
/// - Provide an implementation for [RefCounter::get_refs()] and [RefCounter::set_refs()]
/// ### Example
/// ```rust
/// use grit_counted_refs::RefCounter;
/// 
/// struct MyCounter(usize);
/// 
/// unsafe impl RefCounter for MyCounter {
///     type Inner = usize;
///     const LITERAL_ONE: Self::Inner = 1;
///     const MUT_FROZEN: Self::Inner = usize::MAX;
///     const MUT_ACTIVE: Self::Inner = Self::MUT_FROZEN - 1;
///     const MAX_IMMUT: Self::Inner = Self::MUT_ACTIVE - 1;
///     const NO_REFS: Self::Inner = 0;
/// 
///     #[inline(always)]
///     fn get_refs(&self) -> Self::Inner {
///         self.0
///     }
/// 
///     #[inline(always)]
///     unsafe fn set_refs(&mut self, refs: Self::Inner) {
///         self.0 = refs
///     }
/// }
/// ```
/// # SAFETY
/// Although the above guidelines will serve for most purposes, technically *any* values for the 
/// constants can be supplied, allowing for specialized implementations.
/// 
/// In order to be safe, the constant values provided MUST have the following relationship:  
/// 
/// `LITERAL_ONE == 1 && MUT_FROZEN > MUT_ACTIVE > MAX_IMMUT > NO_REFS`
/// 
/// In addition, while the [RefCounter::set_refs()] method might not contain inherently unsafe code,
/// it must be marked as unsafe to indicate that manually calling it may produce unsafe results
pub unsafe trait RefCounter
where Self::Inner: Ord + Add<Output = Self::Inner> + Sub<Output = Self::Inner> {
    type Inner;
    const LITERAL_ONE: Self::Inner;
    const MUT_FROZEN: Self::Inner;
    const MUT_ACTIVE: Self::Inner;
    const MAX_IMMUT: Self::Inner;
    const NO_REFS: Self::Inner;

    fn get_refs(&self) -> Self::Inner;
    unsafe fn set_refs(&mut self, refs: Self::Inner);

    fn add_imm_ref(&mut self) -> Result<(), RefError> {
        let refs = self.get_refs();
        if refs > Self::MAX_IMMUT {
            return Err(RefError::AlreadyMutablyReferenced)
        }
        if refs == Self::MAX_IMMUT {
            return Err(RefError::MaxImmutableReferences)
        }
        unsafe { self.set_refs(refs + Self::LITERAL_ONE) };
        Ok(())
    }

    fn remove_imm_ref(&mut self) -> Result<(), RefError> {
        let refs = self.get_refs();
        if refs == Self::NO_REFS || refs > Self::MAX_IMMUT {
            return Err(RefError::NotImmutablyReferenced)
        }
        unsafe { self.set_refs(refs - Self::LITERAL_ONE) }
        Ok(())
    }

    fn add_mut_ref(&mut self) -> Result<(), RefError> {
        let refs = self.get_refs();
        if refs >= Self::MUT_ACTIVE {
            return Err(RefError::AlreadyMutablyReferenced)
        }
        if refs > Self::NO_REFS {
            return Err(RefError::StillImmutablyReferenced)
        }
        unsafe { self.set_refs(Self::MUT_ACTIVE) };
        Ok(())
    }

    fn remove_mut_ref(&mut self) -> Result<(), RefError> {
        let refs = self.get_refs();
        if refs == Self::MUT_FROZEN {
            return Err(RefError::ReferenceStillFrozen)
        }
        if refs != Self::MUT_ACTIVE {
            return Err(RefError::NotMutablyReferenced)
        }
        unsafe { self.set_refs(Self::NO_REFS) }
        Ok(())
    }

    fn freeze_mut_ref(&mut self) -> Result<(), RefError> {
        let refs = self.get_refs();
        if refs == Self::MUT_FROZEN {
            return Err(RefError::ReferenceAlreadyFrozen)
        }
        if refs != Self::MUT_ACTIVE {
            return Err(RefError::CanOnlyFreezeMutableRef)
        }
        unsafe { self.set_refs(Self::MUT_FROZEN) }
        Ok(())
    }

    fn unfreeze_mut_ref(&mut self) -> Result<(), RefError> {
        let refs = self.get_refs();
        if refs != Self::MUT_FROZEN {
            return Err(RefError::ReferenceIsntFrozen)
        }
        unsafe { self.set_refs(Self::MUT_ACTIVE) }
        Ok(())
    }

    fn has_no_refs(&self) -> bool {
        self.get_refs() == Self::NO_REFS
    }

    fn is_mutably_referenced(&self) -> bool {
        self.get_refs() >= Self::MUT_ACTIVE
    }

    fn is_immutably_referenced(&self) -> bool {
        let refs = self.get_refs();
        refs >= Self::NO_REFS && refs <= Self::MAX_IMMUT
    }

    fn is_mutably_frozen(&self) -> bool {
        self.get_refs() == Self::MUT_FROZEN
    }
}

pub trait RefCountedValue {
    
}

#[cfg(feature = "impl_primitive_ref_counters")]
macro_rules! impl_ref_counter_primitive {
    ($($T:ty),+) => {
        $(unsafe impl RefCounter for $T {
            type Inner = $T;
            const LITERAL_ONE: Self::Inner = 1;
            const MUT_FROZEN: Self::Inner = Self::Inner::MAX;
            const MUT_ACTIVE: Self::Inner = Self::MUT_FROZEN - 1;
            const MAX_IMMUT: Self::Inner = Self::MUT_ACTIVE - 1;
            const NO_REFS: Self::Inner = Self::Inner::MIN;

            #[inline(always)]
            fn get_refs(&self) -> $T {
                *self
            }
            #[inline(always)]
            unsafe fn set_refs(&mut self, refs: $T) {
                *self = refs
            }
        })+
    };
}

#[cfg(feature = "impl_primitive_ref_counters")]
impl_ref_counter_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, isize, usize);

/// Automatically implement [RefCounter] for a new-type that wraps a `T` where `T` is a primitive integer type
/// 
/// Can be called without specifying a min and max value, resulting in the defaults of T::MIN and T::MAX,
/// or by passing specific min and max values
/// ```rust
/// use grit_counted_refs::{RefCounter, impl_ref_counter_integer_newtype};
/// 
/// struct BigCounter(usize);
/// struct SmallCounterNonZero(u16);
/// 
/// impl_ref_counter_integer_newtype!(BigCounter, usize);
/// impl_ref_counter_integer_newtype!(SmallCounterNonZero, u16, 1, u16::MAX);
/// 
/// let mut big_counter = BigCounter(BigCounter::NO_REFS);
/// let mut small_counter_nonzero = SmallCounterNonZero(SmallCounterNonZero::NO_REFS);
/// 
/// assert_eq!(big_counter.0, BigCounter::NO_REFS);
/// assert_eq!(small_counter_nonzero.0, SmallCounterNonZero::NO_REFS);
/// assert_eq!(small_counter_nonzero.0, 1);
/// 
/// big_counter.add_mut_ref();
/// small_counter_nonzero.add_mut_ref();
/// 
/// assert_eq!(big_counter.0, BigCounter::MUT_ACTIVE);
/// assert_eq!(small_counter_nonzero.0, SmallCounterNonZero::MUT_ACTIVE);
/// ```
#[macro_export]
macro_rules! impl_ref_counter_integer_newtype {
    ($NT:ty, $T:ty) => {
        unsafe impl RefCounter for $NT {
            type Inner = $T;
            const LITERAL_ONE: Self::Inner = 1;
            const MUT_FROZEN: Self::Inner = Self::Inner::MAX;
            const MUT_ACTIVE: Self::Inner = Self::MUT_FROZEN - 1;
            const MAX_IMMUT: Self::Inner = Self::MUT_ACTIVE - 1;
            const NO_REFS: Self::Inner = Self::Inner::MIN;

            #[inline(always)]
            fn get_refs(&self) -> Self::Inner {
                self.0
            }
            #[inline(always)]
            unsafe fn set_refs(&mut self, refs: Self::Inner) {
                self.0 = refs
            }
        }
    };
    ($NT:ty, $T:ty, $MIN:expr, $MAX:expr) => {
        unsafe impl RefCounter for $NT {
            type Inner = $T;
            const LITERAL_ONE: Self::Inner = 1;
            const MUT_FROZEN: Self::Inner = $MAX;
            const MUT_ACTIVE: Self::Inner = Self::MUT_FROZEN - 1;
            const MAX_IMMUT: Self::Inner = Self::MUT_ACTIVE - 1;
            const NO_REFS: Self::Inner = $MIN;

            #[inline(always)]
            fn get_refs(&self) -> Self::Inner {
                self.0
            }
            #[inline(always)]
            unsafe fn set_refs(&mut self, refs: Self::Inner) {
                self.0 = refs
            }
        }
    };
}

pub enum RefError {
    MaxImmutableReferences,
    AccessFrozenReference,
    ReferenceStillFrozen,
    ReferenceAlreadyFrozen,
    ReferenceIsntFrozen,
    StillImmutablyReferenced,
    AlreadyMutablyReferenced,
    CanOnlyFreezeMutableRef,
    NotImmutablyReferenced,
    NotMutablyReferenced
}

#[cfg(test)]
mod tests {
    // use super::*;

   
}
