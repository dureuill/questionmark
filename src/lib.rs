//! Defines an alternative trait to `std::ops::Try`, `Question` that  is not as oriented towards tries and failures.
//!
//! The trait uses a more neutral `ExtractOrReturn` enum to express whether a certain expression `e` should result in some
//! value being returned early, or in some other value being extracted from `e`.
//!
//! Types that implement the `Question` trait can be used with the `q` macro, that is similar to the `std::try` macro.
//! The semantics of `?` could be adapted to use the `Question` trait instead of the `std::ops::Try` trait.

/// Indicate whether we should return early or extract a value
#[must_use]
pub enum ExtractOrReturn<Early, Extract> {
    /// Return early with value of type Early
    ReturnEarly(Early),
    /// Extract value of type Extract
    Extract(Extract),
}

impl<Early, Extract> ExtractOrReturn<Early, Extract> {
    pub fn map_early<U, F>(self, f: F) -> ExtractOrReturn<U, Extract>
    where
        F: FnOnce(Early) -> U,
    {
        match self {
            ExtractOrReturn::ReturnEarly(early) => ExtractOrReturn::ReturnEarly(f(early)),
            ExtractOrReturn::Extract(e) => ExtractOrReturn::Extract(e),
        }
    }

    pub fn map_extract<U, F>(self, f: F) -> ExtractOrReturn<Early, U>
    where
        F: FnOnce(Extract) -> U,
    {
        match self {
            ExtractOrReturn::Extract(extract) => ExtractOrReturn::Extract(f(extract)),
            ExtractOrReturn::ReturnEarly(e) => ExtractOrReturn::ReturnEarly(e),
        }
    }
}

/// Trait to be implemented from types that have a state containing an error,
/// to allow constructing an instance of the type in error state from an instance
/// of the error.
///
/// A prime example of such type is Result<T, E>. From e: E, we can construct Err(e).
pub trait FromError<E> {
    fn from_error(error: E) -> Self;
}

impl<T, E, F> FromError<F> for Result<T, E>
where
    F: std::convert::Into<E>,
{
    fn from_error(error: F) -> Self {
        Err(error.into())
    }
}

/// Marker struct to allow Error types to declare they are convertible from/into None
pub struct NoneError;

impl<T, E> FromError<E> for Option<T>
where
    E: std::convert::Into<NoneError>,
{
    fn from_error(_: E) -> Self {
        None
    }
}

/// Trait to implement to be able to use the `q!` macro on an instance of the type
///
/// A type implementing this trait defines how an instance of this type
/// can be either extracted to the Extract type, or returned early as an instance
/// of the Early type.
pub trait Question<Early> {
    /// The type that should be extracted
    type Extract;

    /// A function to determine if the expression x? should either extract
    /// a value from x of type Extract, or return early a value of type Early.
    /// To do so, this function returns either ReturnEarly(early), or
    /// Extract(extract).
    fn extract_or_return(self) -> ExtractOrReturn<Early, Self::Extract>;
}

/// Macro that stands for the '?' operator.
///
/// # Examples
///
/// Option<T> implements the Question<Option<U>> trait:
///
/// ```
/// #[macro_use]
/// extern crate questionmark;
/// # fn main() {
/// fn maybe_option() -> Option<()> {
///     let _x = q!(Some(42));
///     let _y = q!(None);
///     Some(())
/// }
/// assert_eq!(maybe_option(), None);
/// # }
/// ```
///
/// Note that the `q!` macro should yield identical results to the `?` operator
/// for the types that implement today's `std::ops::Try` trait, so that we could
/// change `?`'s semantics to that of `q!`, the example would then become:
///
/// ```
/// fn maybe_option() -> Option<()> {
///     let _x = Some(42)?;
///     let _y = None?;
///     Some(())
/// }
/// ```
#[macro_export]
macro_rules! q {
    ($e:expr) => {
        match $crate::Question::<_>::extract_or_return($e) {
            $crate::ExtractOrReturn::ReturnEarly(early) => return early,
            $crate::ExtractOrReturn::Extract(extract) => extract,
        }
    };
}

/// Extract T from Result<T, E>, or convert its error to return
/// a Result<U, F> early.
impl<T, U, E, F> Question<Result<U, F>> for Result<T, E>
where
    F: std::convert::From<E>,
{
    type Extract = T;

    fn extract_or_return(self) -> ExtractOrReturn<Result<U, F>, T> {
        match self {
            Ok(ok) => ExtractOrReturn::Extract(ok),
            Err(err) => ExtractOrReturn::ReturnEarly(Err(err.into())),
        }
    }
}

/// Extract T from Option<T>, or return None early.
impl<T, U> Question<Option<U>> for Option<T> {
    type Extract = T;

    fn extract_or_return(self) -> ExtractOrReturn<Option<U>, T> {
        match self {
            Some(u) => ExtractOrReturn::Extract(u),
            None => ExtractOrReturn::ReturnEarly(None),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod bail {
        use super::*;

        struct Bail<T> {
            val: T,
            cond: bool,
        }

        // Continue execution if condition is true, otherwise return early
        fn bail(cond: bool) -> Bail<()> {
            Bail { val: (), cond }
        }

        // Continue execution if condition is true, otherwise return val early
        fn bail_with<T>(cond: bool, val: T) -> Bail<T> {
            Bail { val, cond }
        }

        // Continue execution if condition is true, otherwise return early the stored
        // value
        impl<T> Question<T> for Bail<T> {
            type Extract = ();
            fn extract_or_return(self) -> ExtractOrReturn<T, ()> {
                if self.cond {
                    ExtractOrReturn::Extract(())
                } else {
                    ExtractOrReturn::ReturnEarly(self.val)
                }
            }
        }

        #[test]
        fn test_bail() {
            fn f(x: &mut u32) {
                q!(bail(*x % 2 == 0));
                *x += 1;
            }
            let mut x = 0;
            f(&mut x);
            assert_eq!(x, 1);
            f(&mut x);
            assert_eq!(x, 1);
        }

        #[test]
        fn test_bail_with() {
            fn h() -> usize {
                q!(bail_with(42 == 42, 0));
                q!(bail_with(42 != 42, 1));
                2
            }
            assert_eq!(h(), 1);
        }
    }

    mod result {
        #[derive(Debug, PartialEq, Eq)]
        enum Error {
            Oops(Oops),
            Woops(Woops),
            Arg(Arg),
        }

        #[derive(Debug, PartialEq, Eq)]
        struct Oops;

        #[derive(Debug, PartialEq, Eq)]
        struct Woops;

        #[derive(Debug, PartialEq, Eq)]
        struct Arg;

        impl std::convert::From<Oops> for Error {
            fn from(oops: Oops) -> Self {
                Error::Oops(oops)
            }
        }
        impl std::convert::From<Woops> for Error {
            fn from(woops: Woops) -> Self {
                Error::Woops(woops)
            }
        }
        impl std::convert::From<Arg> for Error {
            fn from(arg: Arg) -> Self {
                Error::Arg(arg)
            }
        }

        #[test]
        fn test_result() {
            fn g() -> Result<(), Error> {
                let _x = q!(Result::<_, Error>::Ok(42));
                let _y = q!(Err(Arg));
                let _z = q!(Err(Woops));
                let _u = q!(Err(Oops));
                Ok(())
            }
            assert_eq!(g(), Err(Error::Arg(Arg)));
        }
    }
}
