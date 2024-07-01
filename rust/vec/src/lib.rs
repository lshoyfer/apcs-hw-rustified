#![allow(warnings)]

use std::{
    alloc::{ alloc, dealloc, handle_alloc_error, realloc, Layout },
    mem::{ self, ManuallyDrop }, 
    ops::{ Deref, DerefMut }, 
    ptr::{ self, NonNull }, 
    marker::PhantomData, 
    slice
};

pub struct Vec<T> {
    buf: RawVec<T>,
    len: usize
}

unsafe impl<T: Send> Send for Vec<T> {}
unsafe impl<T: Sync> Sync for Vec<T> {}

impl<T> Vec<T> {
    pub fn new() -> Vec<T> {
        Vec {
            buf: RawVec::new(),
            len: 0
        }
    }

    fn cap(&self) -> usize {
        self.buf.cap
    }

    fn len(&self) -> usize {
        self.len
    }

    fn ptr(&self) -> *mut T {
        self.buf.ptr.as_ptr()
    }

    fn get(&self, index: usize) -> Option<T> {
        if index >= self.len {
            None
        } else {
            let ptr = self.ptr();
            unsafe { Some(ptr::read(ptr.add(index))) }
        }
    }

    pub fn push(&mut self, value: T) {
        if self.len == self.cap() {
            self.buf.grow();
        }

        let ptr = self.ptr();
        unsafe { ptr::write(ptr.add(self.len), value) };

        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            let ptr = self.ptr();
            unsafe { Some(ptr::read(ptr.add(self.len))) }
        }
    }

    pub fn insert(&mut self, index: usize, element: T) {
        assert!(index <= self.len, "index out of vec bounds");

        if self.len == self.cap() {
            self.buf.grow();
        }

        // [i..len] -> [i+1..len+1]
        unsafe {
            ptr::copy(
                self.ptr().add(index), 
                self.ptr().add(index+1), 
                self.len - index
            );

            ptr::write(self.ptr().add(index), element);
        }

        self.len += 1;
    }

    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of vec bounds");

        self.len -= 1;

        // [index+1..len, index..len-1]
        unsafe {
            let value = ptr::read(self.ptr().add(index));
            ptr::copy(
                self.ptr().add(index+1),
                self.ptr().add(index),
                self.len - index
            );
            value
        }
    }

    pub fn drain(&mut self) -> Drain<'_, T> {
        let res = Drain {
            iter: unsafe { RawValIter::new(self) },
            _marker: PhantomData,
        };
        self.len = 0; // leak protection & may as well early
        res
    }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        let this = ManuallyDrop::new(self);
        unsafe {
            IntoIter {
                iter: RawValIter::new(&this),
                _buf: ptr::read(&this.buf)
            }
        }
    }
}
impl<T> Deref for Vec<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        unsafe { slice::from_raw_parts(self.ptr(), self.len) }
    }
}

impl<T> DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { slice::from_raw_parts_mut(self.ptr(), self.len) }
    }
}

impl<T> Drop for Vec<T> {
    fn drop(&mut self) {
        log::info!("Dropping Vec<T>");
        // for _ in self.drain() {}; 
        while let Some(_) = self.pop() {} // I like the nomicon's idea better
        
        // RawVec<T> handles buffer deallocation (dropped here via dropck glue)
    }
}

pub struct RawVec<T> {
    ptr: NonNull<T>,
    cap: usize,
}

unsafe impl<T: Send> Send for RawVec<T> {}
unsafe impl<T: Sync> Sync for RawVec<T> {}

impl<T> RawVec<T> {
    fn new() -> RawVec<T> {
        let cap = if mem::size_of::<T>() == 0 { usize::MAX } else { 0 };
        RawVec {
            ptr: NonNull::dangling(), // uninit or ZST
            cap
        }
    }
    
    fn grow(&mut self) {
        assert_ne!(mem::size_of::<T>(), 0, "growing ZSTs means capacity overflow as ZSTs set cap to usize::MAX on init");

        // self.cap is guaranteed to be <= isize::MAX on non-ZSTs so this cant overflow
        let new_cap = if self.cap == 0 { 1 } else { self.cap * 2 }; 
        assert!(new_cap <= isize::MAX as usize, "LLVM GEP concerns when sizeof<T>() == 1");
        // when sizeof<T>() > 1 we dont have to worry about overflow -- mem allocator will shit itself first

        let new_layout = Layout::array::<T>(new_cap).unwrap(); 
        let old_layout = Layout::array::<T>(self.cap).unwrap();

        let ptr = if self.cap == 0 {
            unsafe { alloc(new_layout) }
        } else {
            unsafe { realloc(self.ptr.as_ptr().cast(), old_layout, new_layout.size()) }
        };

        
        self.ptr = match NonNull::new(ptr.cast()) {
            Some(p) => p,
            None => handle_alloc_error(new_layout)
        };

        self.cap = new_cap;
    }
}

impl <T> Drop for RawVec<T> {
    fn drop(&mut self) {
        log::info!("Dropping RawVec<T>");
        if self.cap != 0 && mem::size_of::<T>() != 0 {
            let layout = Layout::array::<T>(self.cap).unwrap();
            unsafe { 
                dealloc(self.ptr.as_ptr().cast(), layout);
            }
        }
    }
}

struct Drain<'a, T: 'a> {
    _marker: PhantomData<&'a mut T>,
    iter: RawValIter<T>
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> { self.iter.next_back() }
}

pub struct IntoIter<T> {
    _buf: RawVec<T>, // for drop glue
    iter: RawValIter<T>
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> { self.iter.next_back() }
}

// internal unsafe implementation detail
// also handles dropping for leaks and such, which gives Drain & IntoIter dropck glue.
// The 'nomicon impl's drop directly for Drain and IntoIter, but...!!! I dont think what I did
// here introduces any dropck edge cases............. I think! I'm pretty sure...
struct RawValIter<T> {
    start: *const T,
    end: *const T,
}

impl<T> RawValIter<T> {
    unsafe fn new(slice: &[T]) -> RawValIter<T> {
        RawValIter {
            start: slice.as_ptr(),
            end: if mem::size_of::<T>() == 0 {
                (slice.as_ptr() as usize + slice.len()) as *const _
            } else if slice.len() == 0 { // GEP offset w/ 0 is bad
                slice.as_ptr()
            } else {
                slice.as_ptr().add(slice.len())
            } 
        }
    }
}

impl<T> Iterator for RawValIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        // keep in mind this runs when RawValIter<T> drops
        log::debug!("[RawValIter::next] start: {:?} | end: {:?}", self.start, self.end);
        if self.start != self.end {
            unsafe {
                if mem::size_of::<T>() == 0 {
                    self.start = ((self.start as usize) + 1) as *const _;
                    Some(ptr::read_unaligned(self.start)) // no-op for ZSTs
                } else {
                    let old_ptr = self.start;
                    self.start = self.start.add(1);
                    Some(ptr::read(old_ptr))
                }
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let type_size = mem::size_of::<T>();
        let type_size = if type_size == 0 { 1 } else { type_size };
        let len = ((self.end as usize) - (self.start as usize)) / type_size;
        (len, Some(len))
    }
}
impl<T> DoubleEndedIterator for RawValIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start != self.end {
            unsafe {
                self.end = if mem::size_of::<T>() != 0 {
                    self.end.offset(-1)
                } else {
                    ((self.end as usize) - 1) as *const _
                };
                Some(ptr::read(self.end))
            }
        } else {
            None
        } 
    }
}

impl<T> Drop for RawValIter<T> {
    fn drop(&mut self) {
        log::info!("Dropping RawValIter<T>");
        for _ in self {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use log::trace;

    macro_rules! log_prelude {
        () => { 
            // NOTE: if you want to log sensibly, use single-threaded test runner or run `vec/test_runner.sh <test-regex>`
            let _ = simple_logger::SimpleLogger::new().without_timestamps().init();
        };
    }

    #[test]
    fn vect_drain() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(5);
        foo.push(4);
        foo.push(3);
        foo.push(3);
        foo.push(4);
        foo.push(6);

        let foo_copied: std::vec::Vec<i32> = foo.iter().copied().collect();
        trace!(
            "Pre-Drain: {:?} | len: {:?} | bufp: {:?} | *bufp: {:?} | cap: {:?}",
            foo_copied, foo.len, foo.ptr(), unsafe { *foo.ptr() }, foo.cap()
        );

        for x in foo.drain() {
            trace!("Vec::drain {x}");
        };

        let foo_copied: std::vec::Vec<i32> = foo.iter().copied().collect();
        trace!(
            "Post-Drain: {:?} | len: {:?} | bufp: {:?} | *bufp: {:?} | cap: {:?}",
            foo_copied, foo.len, foo.ptr(), unsafe { *foo.ptr() }, foo.cap()
        );

        for x in foo.drain() {
            trace!("Vec::drain {x}"); // should be a no-op
        };

        assert_eq!(foo_copied, vec![], "vec was properly drained");
        assert_eq!(foo.cap(), 8, "vec still has allocated capacity");

        let mut new_foo = Vec::new();

        new_foo.push(String::from("hey1"));
        new_foo.push(String::from("hey2"));
        new_foo.push(String::from("hey3"));
        new_foo.push(String::from("hey4"));
        new_foo.push(String::from("hey5"));

        let drainer = new_foo.drain();
        std::mem::forget(drainer); // leak drainer

        let new_foo_copied: std::vec::Vec<i32> = foo.iter().copied().collect();
        trace!(
            "Post-Drain-Leak: {:?} | len: {:?} | bufp: {:?} | *bufp: {:?} | cap: {:?}",
            new_foo_copied, new_foo.len, new_foo.ptr(), unsafe { ManuallyDrop::new(std::ptr::read(new_foo.ptr())) }, new_foo.cap()
        );

        assert_eq!(new_foo_copied, vec![], "drain leaked foo's resources but foo's len was properly adjusted for safety and cannot access its values following a drain");
    }

    #[test] 
    // actually this could just seg fault etc LOL tho it doesnt seem to on my m1 mac (which seems to give a consistent deref'd dummy value)
    #[should_panic = "accessing raw ptr to dealloc'd memory"]
    // #[should_seg_fault = "yep"]
    fn vect_into_iter_properly_deallocs_buf() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(5);
        foo.push(4);
        foo.push(3);
        foo.push(3);
        foo.push(4);
        foo.push(6);

        let buf = ManuallyDrop::new(unsafe { std::ptr::read(&foo.buf as *const RawVec<_>) });

        let mut iter = foo.into_iter();

        unsafe {
            trace!("buf still alive >>> p: {:?} | *p: {:?} | cap: {:?}", (*buf).ptr, *(*buf).ptr.as_ptr(), (*buf).cap);
        };

        for _ in iter {};

        // this may seg fault etc etc !!! which would be a valid (desired) behavior of the test rofl
        unsafe {
            trace!("buf dead >>> p: {:?} | *p: {:?} | cap: {:?}", (*buf).ptr, *(*buf).ptr.as_ptr(), (*buf).cap);

            if *(*buf).ptr.as_ptr() != 5 {
                panic!("accessing raw ptr to dealloc'd memory");
                // Good! This dealloc'd properly & we also are lucky enough to still be
                // able to even read the garbage memory to properly unwind for the test.
            }
        }
    }

    #[test]
    fn vect_into_iter() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(5);
        foo.push(4);
        foo.push(3);
        foo.push(3);
        foo.push(4);
        foo.push(6);

        for x in foo.into_iter() {
            trace!("Vec::into_iter() {x}");
        }

        let mut foo = Vec::new();
        foo.push(5);
        foo.push(4);
        foo.push(3);
        foo.push(3);
        foo.push(4);
        foo.push(6);

        let test_collec = [5, 4, 3, 3, 4, 6];
        let iter = foo.into_iter();
        let test_iter = test_collec.into_iter();
        for (original, test) in iter.zip(test_iter) {
            assert_eq!(original, test, "Vec<T> properly iterates expected value via into_iter()");
        }
    }

    #[test]
    fn vect_slice_iters() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(5);
        foo.push(4);
        foo.push(3);
        foo.push(3);
        foo.push(4);
        foo.push(6);

        for x in foo.iter() {
            trace!("(&[T]).iter() {x}");
        }

        for x in foo.iter_mut() {
            trace!("(&mut [T]).iter_mut() {x}");
        }

        let test_collec = [5, 4, 3, 3, 4, 6];
        let iter = foo.iter();
        let test_iter = test_collec.iter();
        for (original, test) in iter.zip(test_iter) {
            assert_eq!(*original, *test, "Vec<T> properly iterates expected values via Deref coercion to slices");
        }
    }

    #[test]
    fn vect_push_access_pop() {
        log_prelude!();

        let mut foo = Vec::new();

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );

        foo.push(5u8);

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );

        let mut pop_collection: std::vec::Vec<Option<u8>> = std::vec![];
        let mut collect = |val: Option<u8>| pop_collection.push(val);
        
        foo.push(6u8);
        foo.push(7u8);
        foo.push(8u8);
        foo.push(9u8);
        collect(foo.pop());
        collect(foo.pop());
        foo.push(10u8);
        foo.push(255u8);

        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap
        );

        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());

        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?} | POPS: {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap,
            pop_collection
        ); 
    
        assert_eq!(
            pop_collection,
            vec![Some(9), Some(8), Some(255), Some(10), Some(7), Some(6), Some(5), None, None, None, None, None],
            "vec .pop()ed expected values in expected order"
        );
        assert_eq!(&foo[..], &[], "vec was emptied after calling more than enough .pop()s")
    }

    #[test]
    fn vect_insert_access_remove() {
        log_prelude!();

        let mut foo: Vec<u64> = Vec::new();
        let mut remove_collection: std::vec::Vec<u64> = std::vec![];
        let mut collect = |val: u64| remove_collection.push(val);

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );

        foo.insert(0, 1337); // [1337]

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );


        foo.insert(1, 62345); // [1337, 62345] 
        foo.insert(1, 2665); // [1337, 2665, 62345]  
        foo.insert(0, 57); // [57, 1337, 2665, 62345]  
        foo.insert(2, 2024); // [57, 1337, 2024, 2665, 62345]  


        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap
        );

        collect(foo.remove(0)); // [1337, 2024, 2665, 62345]
        collect(foo.remove(2)); // [1337, 2024, 62345]
        foo.insert(2, 2776); // [1337, 2024, 2776, 62345]
        assert_eq!(&foo[..], &[1337, 2024, 2776, 62345], "vec properly .inserts and .removes items");
        collect(foo.remove(1)); // [1337, 2776, 62345]
        collect(foo.remove(2)); // [1337, 2776]
        collect(foo.remove(1)); // [1337]
        collect(foo.remove(0)); // []


        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?} | POPS: {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap,
            remove_collection
        );

        assert_eq!(remove_collection, vec![57, 2665, 2024, 62345, 2776, 1337], "vec .removed correct items in expected order");
        assert_eq!(&foo[..], &[], "vec is empty after .removing all items");
    }

    #[test]
    fn raw_vec_alloc_dealloc_u8() {
        log_prelude!();

        let mut foo = unsafe { mem::ManuallyDrop::new(RawVec::<u8>::new()) };
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        foo.grow();
        foo.grow();
        foo.grow();
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        foo.grow();
        foo.grow();
        foo.grow();
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        // let viewer = &*foo as *const RawVec<_>;
        unsafe {
            let foo = ManuallyDrop::into_inner(foo);
            mem::drop(foo);
            // may abort since we are reading possibly reclaimed memory tho effectively what I am reading *should* still be on the stack
            // but yeah this is pretty stupid lol
            // trace!("Post Drop | {:?} {:?}", (*viewer).ptr, (*viewer).cap);
        }
    }

    #[test]
    fn raw_vec_alloc_dealloc_u64() {
        log_prelude!();

        let mut foo = unsafe { mem::ManuallyDrop::new(RawVec::<u64>::new()) };
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        foo.grow();
        foo.grow();
        foo.grow();
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        foo.grow();
        foo.grow();
        foo.grow();
        trace!("{:?} {:?}", foo.ptr, foo.cap);

        // let viewer = &*foo as *const RawVec<_>;
        unsafe {
            let foo = ManuallyDrop::into_inner(foo);
            mem::drop(foo);
            // may abort since we are reading possibly reclaimed memory tho effectively what I am reading *should* 
            // basically 100% still be on the stack but yeah this is pretty stupid lol
            // trace!("Post Drop | {:?} {:?}", (*viewer).ptr, (*viewer).cap);
        }
    }

    // #[test]
    // this will abort the process so I cant really test for it here via catching it since there is no unwind but I did confirm it aborts
    // -- i'll leave it here just for its own sake
    fn raw_vec_cap_overflow_u8() {
        log_prelude!();


        std::thread::spawn(|| {
            let mut foo = unsafe { RawVec::<u8>::new() };
            trace!("constructor {:?} {:?}", foo.ptr, foo.cap);

            foo.grow();
            trace!("init alloc grow {:?} {:?}", foo.ptr, foo.cap);

            foo.cap = isize::MAX as usize / 2;
            trace!("cap increase {:?} {:?}", foo.ptr, foo.cap);
    
            foo.grow(); // aborts the process
            trace!("post cap overflow {:?} {:?}", foo.ptr, foo.cap);
        });
    }

    #[test]
    #[should_panic = "called `Result::unwrap()` on an `Err` value: LayoutError"]
    fn raw_vec_cap_overflow_u16() {
        log_prelude!();

        let mut foo = unsafe { RawVec::<u16>::new() };
        trace!("constructor {:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        trace!("init alloc grow {:?} {:?}", foo.ptr, foo.cap);

        foo.cap = isize::MAX as usize / 2;
        trace!("cap increase {:?} {:?}", foo.ptr, foo.cap);
    
        foo.grow();
        trace!("post cap overflow {:?} {:?}", foo.ptr, foo.cap); // shouldnt run
    }

    #[test]
    fn ZST_vect_drain() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());

        let foo_copied: std::vec::Vec<()> = foo.iter().copied().collect();
        trace!(
            "Pre-Drain: {:?} | len: {:?} | bufp: {:?} | *bufp: {:?} | cap: {:?}",
            foo_copied, foo.len, foo.ptr(), unsafe { *foo.ptr() }, foo.cap()
        );

        log::info!("About to First Drain");
        for x in foo.drain() {
            trace!("Vec::drain {x:?}");
        };

        let foo_copied: std::vec::Vec<()> = foo.iter().copied().collect();
        trace!(
            "Post-Drain: {:?} | len: {:?} | bufp: {:?} | *bufp: {:?} | cap: {:?}",
            foo_copied, foo.len, foo.ptr(), unsafe { *foo.ptr() }, foo.cap()
        );

        for x in foo.drain() {
            trace!("Vec::drain {x:?}"); // should be a no-op
        };

        assert_eq!(foo_copied, vec![], "vec was properly drained");
        assert_eq!(foo.cap(), usize::MAX, "vec still has 'allocated' capacity");

        let mut new_foo = Vec::new();

        new_foo.push(());
        new_foo.push(());
        new_foo.push(());
        new_foo.push(());
        new_foo.push(());

        let drainer = new_foo.drain();
        std::mem::forget(drainer); // leak drainer

        let new_foo_copied: std::vec::Vec<()> = new_foo.iter().copied().collect();
        trace!(
            "Post-Drain-Leak: {:?} | len: {:?} | bufp: {:?} | *bufp: {:?} | cap: {:?}",
            new_foo_copied, new_foo.len, new_foo.ptr(), unsafe { ManuallyDrop::new(std::ptr::read(new_foo.ptr())) }, new_foo.cap()
        );

        assert_eq!(new_foo_copied, vec![], "drain leaked foo's resources but foo's len was properly adjusted for safety and cannot access its values following a drain");
    }

    #[test] 
    fn ZST_vect_into_iter_drop() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());

        let buf = ManuallyDrop::new(unsafe { std::ptr::read(&foo.buf as *const RawVec<_>) });

        let mut iter = foo.into_iter();

        unsafe {
            trace!("buf still alive >>> p: {:?} | *p: {:?} | cap: {:?}", (*buf).ptr, *(*buf).ptr.as_ptr(), (*buf).cap);
        };

        for _ in iter {};

        unsafe {
            trace!("buf dead >>> p: {:?} | *p: {:?} | cap: {:?}", (*buf).ptr, *(*buf).ptr.as_ptr(), (*buf).cap);

            assert_eq!(
                *(*buf).ptr.as_ptr(),
                (), 
                "buf dead but not actually dropped (given garbage) b/c ZST vec's are always dangling \
                & dont alloc & rust compiler/type system will always give me () on an aligned non-null () ptr
                -- or at least my intuition hopes so hahah... seems like on a type level this is safe, alas."
            );
        }
    }

    #[test]
    fn ZST_vect_into_iter() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());

        for x in foo.into_iter() {
            trace!("Vec::into_iter() {x:?}");
        }

        let mut foo = Vec::new();
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());

        let test_collec = [(), (), (), (), (), ()];
        let iter = foo.into_iter();
        let test_iter = test_collec.into_iter();
        for (original, test) in iter.zip(test_iter) {
            assert_eq!(original, test, "Vec<T> properly iterates expected value via into_iter()");
        }
    }

    #[test]
    fn ZST_vect_slice_iters() {
        log_prelude!();

        let mut foo = Vec::new();
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());

        for x in foo.iter() {
            trace!("(&[T]).iter() {x:?}");
        }

        for x in foo.iter_mut() {
            trace!("(&mut [T]).iter_mut() {x:?}");
        }

        let test_collec = [(), (), (), (), (), ()];
        let iter = foo.iter();
        let test_iter = test_collec.iter();
        for (original, test) in iter.zip(test_iter) {
            assert_eq!(*original, *test, "Vec<T> properly iterates expected values via Deref coercion to slices");
        }
    }

    #[test]
    fn ZST_vect_push_access_pop() {
        log_prelude!();

        let mut foo = Vec::new();

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );

        foo.push(());

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );

        let mut pop_collection: std::vec::Vec<Option<()>> = std::vec![];
        let mut collect = |val: Option<()>| pop_collection.push(val);
        
        foo.push(());
        foo.push(());
        foo.push(());
        foo.push(());
        collect(foo.pop());
        collect(foo.pop());
        assert_eq!(&foo[..], &[(), (), ()], "5 () were added, 2 were popped");
        foo.push(());
        foo.push(());

        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap
        );

        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());
        collect(foo.pop());

        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?} | POPS: {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap,
            pop_collection
        ); 

        assert_eq!(
            pop_collection,
            vec![Some(()), Some(()), Some(()), Some(()), Some(()), Some(()), Some(()), None, None, None, None, None],
            "popped 7 ()'s, & 5 on empty zst vec (yielding None)"
        );
        assert_eq!(&foo[..], &[], "all () were popped from zst vec");
    }

    #[test]
    fn ZST_vect_insert_access_remove() {
        log_prelude!();

        let mut foo: Vec<()> = Vec::new();
        let mut remove_collection: std::vec::Vec<()> = std::vec![];
        let mut collect = |val: ()| remove_collection.push(val);

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );

        foo.insert(0, ()); // [()]

        trace!(
            "VEC LEN: {:?} | VEC[0]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            foo.get(0),
            foo.buf.ptr, foo.buf.cap
        );


        foo.insert(1, ()); // [(), ()] 
        foo.insert(1, ()); // [(), (), ()]  
        foo.insert(0, ()); // [(), (), (), ()]  
        foo.insert(2, ()); // [(), (), (), (), ()]  


        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap
        );

        collect(foo.remove(0)); 
        collect(foo.remove(2)); 
        foo.insert(2, ()); 
        assert_eq!(&foo[..], &[(), (), (), ()], "two units were removed properly & 1 was added");
        collect(foo.remove(1)); 
        collect(foo.remove(2)); 
        collect(foo.remove(1)); 
        collect(foo.remove(0)); 


        trace!(
            "VEC LEN: {:?} | VEC[..]: {:?} | BUF: {:?} {:?} | POPS: {:?}",
            foo.len(),
            [foo.get(0), foo.get(1), foo.get(2), foo.get(3), foo.get(4), foo.get(5), foo.get(6)],
            foo.buf.ptr, foo.buf.cap,
            remove_collection
        ); 

        assert_eq!(remove_collection, vec![(), (), (), (), (), ()], "all removed");
        assert_eq!(&foo[..], &[], "all removed");
    }

    #[test]
    #[should_panic] // Vec w/ ZSTs should never grow capacity
    fn ZST_raw_vec_cap_overflow() {
        log_prelude!();

        let mut foo = unsafe { RawVec::<()>::new() };
        trace!("constructor {:?} {:?}", foo.ptr, foo.cap);

        foo.grow();
        trace!("init alloc grow {:?} {:?}", foo.ptr, foo.cap); 
    }
}