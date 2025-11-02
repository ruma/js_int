use crate::Int;
use core::sync::atomic::{AtomicI64, Ordering};

pub struct AtomicInt(AtomicI64);

impl AtomicInt {
    // TODO: const
    pub fn new(value: Int) -> Self {
        Self(AtomicI64::new(value.into()))
    }

    // from_ptr is only possible if the types are #[repr(transparent)]
    // get_mut is only possible if the types are #[repr(transparent)]
    // as_ptr is only possible if the types are #[repr(transparent)]

    pub fn into_inner(self) -> Int {
        let value = self.0.into_inner();
        // SAFETY: AtomicInt upholds the invariant that it's content is in the range of Int
        unsafe { Int::new_unchecked(value) }
    }

    pub fn load(&self, order: Ordering) -> Int {
        let value = self.0.load(order);
        // SAFETY: AtomicInt upholds the invariant that it's content is in the range of Int
        unsafe { Int::new_unchecked(value) }
    }

    pub fn store(&self, value: Int, order: Ordering) {
        self.0.store(value.into(), order);
    }

    pub fn swap(&self, value: Int, order: Ordering) -> Int {
        let value = self.0.swap(value.into(), order);
        // SAFETY: AtomicInt upholds the invariant that it's content is in the range of Int
        unsafe { Int::new_unchecked(value) }
    }

    pub fn compare_exchange(
        &self,
        current: Int,
        new: Int,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Int, Int> {
        let result = self.0.compare_exchange(current.into(), new.into(), success, failure);
        // SAFETY: AtomicInt upholds the invariant that it's content is in the range of Int
        unsafe {
            result.map(|value| Int::new_unchecked(value)).map_err(|value| Int::new_unchecked(value))
        }
    }

    pub fn compare_exchange_weak(
        &self,
        current: Int,
        new: Int,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Int, Int> {
        let result = self.0.compare_exchange_weak(current.into(), new.into(), success, failure);
        // SAFETY: AtomicInt upholds the invariant that it's content is in the range of Int
        unsafe {
            result.map(|value| Int::new_unchecked(value)).map_err(|value| Int::new_unchecked(value))
        }
    }

    // TODO: fetch_add
    // TODO: fetch_sub
    // TODO: fetch_and
    // TODO: fetch_nand
    // TODO: fetch_or
    // TODO: fetch_xor

    pub fn fetch_update<F>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        f: F,
    ) -> Result<Int, Int> {
        todo!()
    }

    pub fn fetch_max(&self, value: Int, order: Ordering) -> Int {
        let max = self.0.fetch_max(value.into(), order);

        // SAFETY: AtomicInt upholds the invariant that it's content is in the range of Int
        unsafe { Int::new_unchecked(max) }
    }

    pub fn fetch_min(&self, value: Int, order: Ordering) -> Int {
        let min = self.0.fetch_min(value.into(), order);

        // SAFETY: AtomicInt upholds the invariant that it's content is in the range of Int
        unsafe { Int::new_unchecked(min) }
    }
}
