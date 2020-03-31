//! Defines an alternative trait to `std::ops::Try`, `TryUnwrap` that  is not as oriented towards tries and failures.
//!
//! The trait uses a more neutral `MaybeUnwrap` enum to express whether a certain expression `e` should result in some
//! value being returned early, or in some other value being unwrapped from `e`.
//!
//! Types that implement the `TryUnwrap` trait can be used with the `q` macro, that is similar to the `std::try` macro.
//! The semantics of `?` could be adapted to use the `TryUnwrap` trait instead of the `std::ops::Try` trait.

/// Indicate whether we should return early or unwrap a value
#[must_use]
pub enum MaybeUnwrap<T, E> {
    /// Unwrap value of type T
    Unwrap(T),
    /// Return early with value of type E
    Return(E),
}

impl<T, E> MaybeUnwrap<T, E> {
    pub fn map_unwrap<U, F>(self, f: F) -> MaybeUnwrap<U, E>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            MaybeUnwrap::Unwrap(t) => MaybeUnwrap::Unwrap(f(t)),
            MaybeUnwrap::Return(early) => MaybeUnwrap::Return(early),
        }
    }

    pub fn map_return<U, F>(self, f: F) -> MaybeUnwrap<T, U>
    where
        F: FnOnce(E) -> U,
    {
        match self {
            MaybeUnwrap::Return(early) => MaybeUnwrap::Return(f(early)),
            MaybeUnwrap::Unwrap(t) => MaybeUnwrap::Unwrap(t),
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
/// can be either unwrapped to the Output type, or returned early as an instance
/// of the Return type.
pub trait TryUnwrap<Return> {
    /// The type that should be unwrapped
    type Output;

    /// A function to determine if the expression x? should either unwrap
    /// a value from x of type Output, or return early a value of type Return.
    /// To do so, this function returns either Return(early), or
    /// Unwrap(t).
    fn try_unwrap(self) -> MaybeUnwrap<Self::Output, Return>;

    // A function to "go back" from the produced output to
    // the wrapping value.
    fn from_unwrapped(output: Self::Output) -> Self;
}

/// Macro that stands for the '?' operator.
///
/// # Examples
///
/// Option<T> implements the TryUnwrap<Option<U>> trait:
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
        match $crate::TryUnwrap::<_>::try_unwrap($e) {
            $crate::MaybeUnwrap::Return(early) => return early,
            $crate::MaybeUnwrap::Unwrap(t) => t,
        }
    };
}

/// Unwrap T from Result<T, E>, or convert its error to return
/// a compatible error type early.
impl<T, E, F> TryUnwrap<F> for Result<T, E>
where
    F: FromError<E>,
{
    type Output = T;

    fn try_unwrap(self) -> MaybeUnwrap<T, F> {
        match self {
            Ok(ok) => MaybeUnwrap::Unwrap(ok),
            Err(err) => MaybeUnwrap::Return(FromError::from_error(err)),
        }
    }

    fn from_unwrapped(output: Self::Output) -> Self {
        Ok(output)
    }
}

/// Unwrap T from Option<T>, or return a compatible error type early.
impl<T, F: FromError<NoneError>> TryUnwrap<F> for Option<T> {
    type Output = T;

    fn try_unwrap(self) -> MaybeUnwrap<T, F> {
        match self {
            Some(u) => MaybeUnwrap::Unwrap(u),
            None => MaybeUnwrap::Return(FromError::from_error(NoneError)),
        }
    }

    fn from_unwrapped(output: Self::Output) -> Self {
        Some(output)
    }
}

use core::task::Poll;

// Unwrap Poll::Pending if the future isn't ready, or Poll::Ready(T::Output)
// if the underlying future is ready and was unwrapped, or return early if the
// polled type wants to return early.
impl<T, F> TryUnwrap<F> for Poll<T>
where
    T: TryUnwrap<F>,
{
    type Output = Poll<T::Output>;

    fn try_unwrap(self) -> MaybeUnwrap<Self::Output, F> {
        match self {
            Poll::Pending => MaybeUnwrap::Unwrap(Poll::Pending),
            Poll::Ready(t) => t
                .try_unwrap()
                .map_unwrap(|output| Poll::Ready(output)),
        }
    }

    fn from_unwrapped(output: Self::Output) -> Self {
        match output {
            Poll::Pending => Poll::Pending,
            Poll::Ready(output) => Poll::Ready(T::from_unwrapped(output)),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod bail {
        use super::*;

        struct Bail<T>(Option<T>);

        // Continue execution if condition is true, otherwise return early
        fn bail(cond: bool) -> Bail<()> {
            bail_with(cond, ())
        }

        // Continue execution if condition is true, otherwise return val early
        fn bail_with<T>(cond: bool, val: T) -> Bail<T> {
            Bail(if cond {
                None // continue execution
            } else {
                Some(val) // return 'val' early
            })
        }

        // Continue execution if condition is true, otherwise return early the stored
        // value
        impl<T> TryUnwrap<T> for Bail<T> {
            type Output = ();
            fn try_unwrap(self) -> MaybeUnwrap<(), T> {
                match self {
                    Bail(Some(value)) => MaybeUnwrap::Return(value),
                    Bail(None) => MaybeUnwrap::Unwrap(()),
                }
            }

            fn from_unwrapped((): ()) -> Self {
                Bail(None)
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

    #[derive(Debug, PartialEq, Eq)]
    enum Error {
        Oops(Oops),
        Woops(Woops),
        Arg(Arg),
        None,
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

    mod result {
        use super::*;

        #[test]
        fn test_result() {
            fn g() -> Result<(), Error> {
                let _x = q!(Result::<_, Error>::Ok(42));
                let _y = q!(Err(Arg));
                let _z = q!(Err(Woops));
                let _u = q!(Err(Oops));
                let _v = q!(Err(Error::Oops(Oops)));
                Ok(())
            }
            assert_eq!(g(), Err(Error::Arg(Arg)));
        }

        impl Into<crate::NoneError> for Error {
            fn into(self) -> crate::NoneError {
                crate::NoneError
            }
        }

        impl From<crate::NoneError> for Error {
            fn from(_: crate::NoneError) -> Self {
                Error::None
            }
        }

        #[test]
        fn test_result_option() {
            fn res_to_option() -> Option<()> {
                let _x = q!(Err(Error::Arg(Arg)));
                Some(())
            }

            fn option_to_res() -> Result<(), Error> {
                q!(None);
                Ok(())
            }

            assert_eq!(res_to_option(), None);
            assert_eq!(option_to_res(), Err(Error::None));
        }
    }

    mod poll {
        use super::*;
        use core::task::Poll;
        #[test]
        fn test_poll() {
            // from @steffahn in https://internals.rust-lang.org/t/a-slightly-more-general-easier-to-implement-alternative-to-the-try-trait/12034/3
            fn foo() -> Result<(), Error> {
                let _x: Poll<u32> = Poll::Ready(Err(Arg))?;
                Ok(())
            }

            fn bar() -> Result<(), Error> {
                let _x: Poll<Option<u32>> = Poll::Ready(Some(Err(Oops)))?;
                Ok(())
            }

            fn qux() -> Poll<Result<(), Error>> {
                let _x: i32 = Err(Woops)?;
                Poll::Pending
            }

            fn baz() -> Poll<Option<Result<(), Error>>> {
                let _x: i32 = Err(Error::None)?;
                Poll::Pending
            }

            assert_eq!(foo(), Err(Error::Arg(Arg)));
            assert_eq!(bar(), Err(Error::Oops(Oops)));
            assert_eq!(qux(), Poll::Ready(Err(Error::Woops(Woops))));
            assert_eq!(baz(), Poll::Ready(Some(Err(Error::None))));
        }
    }
}
