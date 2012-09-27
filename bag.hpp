// Copyright (c) 2012, Mattia Penati <mattia.penati@gmail.com>
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
//  * Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//
//  * Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#ifndef BAG_HPP
#define BAG_HPP

// ===========================================================================
// Configuration
// ===========================================================================
#define BAG_BEGIN_NAMESPACE namespace bag {
#define BAG_END_NAMESPACE }

#ifndef BAG_DEFAULT_TYPE
#define BAG_DEFAULT_TYPE double
#endif // BAG_DEFAULT_TYPE

// ===========================================================================
// Macro
// ===========================================================================
#define RETURNS(...)                                                         \
  -> decltype(__VA_ARGS__) { return(__VA_ARGS__); }                          \
/**/
#define RETURNS_IF(Condition, ...)                                           \
  -> typename util::enable_if<Condition,decltype(__VA_ARGS__)>::type         \
  { return(__VA_ARGS__); }                                                   \
/**/

#define BAG_CAT(A,B) BAG_CAT1(A,B)
#define BAG_CAT1(A,B) BAG_CAT2(A ## B)
#define BAG_CAT2(A) A

#define BAG_TUPLE_REM(Args) BAG_TUPLE_REM1 Args
#define BAG_TUPLE_REM1(...) __VA_ARGS__

// ===========================================================================
// Headers
// ===========================================================================
#ifndef BAG_DONT_USE_CMATH
#include <cmath>
#endif // BAG_DONT_USE_CMATH

// ===========================================================================
// Code
// ===========================================================================
BAG_BEGIN_NAMESPACE

// ===========================================================================
// Utilities
// ===========================================================================

// some utilities
namespace util {
  // integral constant
  template <class T, T Value>
  struct integral_c
    { static constexpr T value = Value; };

  // boolean constants
  typedef integral_c<bool, true > true_;
  typedef integral_c<bool, false> false_;

  // enable_if
  template <bool Condition, class Type = void> struct enable_if;
  template <class Type> struct enable_if<true,Type> { typedef Type type; };

  // add_rvalue_ref
  template <class T> struct add_rvalue_ref { typedef T && type; };

  // remove_ref
  template <class T> struct remove_ref      { typedef T type; };
  template <class T> struct remove_ref<T&>  { typedef T type; };
  template <class T> struct remove_ref<T&&> { typedef T type; };

  // remove_const
  template <class T> struct remove_const          { typedef T type; };
  template <class T> struct remove_const<T const> { typedef T type; };

  // remove_volatile
  template <class T> struct remove_volatile             { typedef T type; };
  template <class T> struct remove_volatile<T volatile> { typedef T type; };

  // remove_cv
  template <class T> struct remove_cv
    : remove_const<typename remove_volatile<T>::type> {};

  // decay
  template <class T> struct decay
    : remove_cv<typename remove_ref<T>::type> {};

  // add_const
  template <class T> struct add_const          { typedef T const type; };
  template <class T> struct add_const<T const> { typedef T const type; };

  // forward
  template <class T>
  constexpr inline T && forward(typename remove_ref<T>::type & f)
    { return(static_cast<T &&>(f)); }
  template <class T>
  constexpr inline T && forward(typename remove_ref<T>::type && f)
    { return(static_cast<T &&>(f)); }

  // move
  template <class T>
  constexpr inline typename remove_ref<T>::type && move(T && f)
    { return(static_cast<typename remove_ref<T>::type &&>(f));}

  // declval
  template <class T>
  constexpr typename add_rvalue_ref<T>::type declval();

  // min
  template <class T>
  constexpr inline T const & min(T const & x, T const & y)
    { return((x < y) ? x : y); }

  // max
  template <class T>
  constexpr inline T const & max(T const & x, T const & y)
    { return((x < y) ? y : x); }

  // forward declaration
  template <class... Types> struct tuple;

  // tuple size
  template <class Tuple>
  struct tuple_size;
  template <class... Types>
  struct tuple_size< tuple<Types...> >
    { static constexpr auto value = sizeof...(Types); };

  // tuple_element
  template <int I, class Tuple> struct tuple_element;
  template <class First, class... Tail>
  struct tuple_element<0, tuple<First,Tail...> >
    { typedef First type; };
  template <int N, class First, class... Tail>
  struct tuple_element<N, tuple<First,Tail...> >
    : tuple_element<N-1, tuple<Tail...> > {};

  // tuple leaf
  template <int I, class T>
  struct tuple_leaf__ {
    T value;

    // constructors
    constexpr inline tuple_leaf__() = default;

    template <class U>
    constexpr inline explicit tuple_leaf__(U && x)
      : value(forward<U>(x)) {}

    // extracts value
    inline T & get() { return(value); }
    constexpr inline T const & get() { return(value); }
  };

  // tuple indices
  template <int... > struct tuple_indices__ {};

  // make tuple indices
  template <int N, class = tuple_indices__<> >
  struct make_tuple_indices__;
  template <int N, int... I>
  struct make_tuple_indices__<N, tuple_indices__<I...> >
    : make_tuple_indices__<N-1, tuple_indices__<N-1,I...> > {};
  template <int... I>
  struct make_tuple_indices__<0, tuple_indices__<I...> > {
    typedef tuple_indices__<I...> type;
  };

  // implementation
  template <class Indices, class... Types> struct tuple_impl__;

  template <int... I, class... T>
  struct tuple_impl__<tuple_indices__<I...>, T...>
    : tuple_leaf__<I,T>...
  {
    typedef tuple_indices__<I...> indices__;

    // constructors
    template <class... U>
    constexpr inline explicit tuple_impl__(U &&... args)
      : tuple_leaf__<I,T>(forward<U>(args))... {}
  };

  // retrieves the Jth element of a tuple
  template <int J, class I, class... T>
  constexpr inline typename tuple_element< J, tuple<T...> >::type &&
  get(tuple_impl__<I,T...> && t)
  {
    typedef typename tuple_element< J, tuple<T...> >::type type__;
    return(static_cast<type__ &&>(
      static_cast<tuple_leaf__<J,type__> &&>(t).get()));
  }
  template <int J, class I, class... T>
  constexpr inline typename tuple_element< J, tuple<T...> >::type &
  get(tuple_impl__<I,T...> & t)
  {
    typedef typename tuple_element< J, tuple<T...> >::type type__;
    return(static_cast<tuple_leaf__<J,type__> &>(t).get());
  }
  template <int J, class I, class... T>
  constexpr inline typename tuple_element< J, tuple<T...> >::type const &
  get(tuple_impl__<I,T...> const & t)
  {
    typedef typename tuple_element< J, tuple<T...> >::type type__;
    return(static_cast<tuple_leaf__<J,type__> const &>(t).get());
  }

  // tuple
  template <class... T>
  struct tuple
    : tuple_impl__<typename make_tuple_indices__<sizeof...(T)>::type, T...>
  {
    typedef typename make_tuple_indices__<sizeof...(T)>::type indices__;
    typedef tuple_impl__<indices__, T...> base__;

    template <class... Args>
    constexpr inline tuple(Args &&... args)
      : base__(forward<Args>(args)...) {}
  };

  // make_tuple
  template <class... Args>
  constexpr inline auto make_tuple(Args &&... args)
    RETURNS(tuple<typename decay<Args>::type...>(forward<Args>(args)...))

  // forward_as_tuple
  template <class... Args>
  constexpr inline auto forward_as_tuple(Args &&... args)
    RETURNS(tuple<Args &&...>(forward<Args>(args)...))

  // apply_to_tuple
  template <class Function, class Tuple, int... I>
  constexpr inline auto apply_to_tuple_impl__(Function && f,
                                              Tuple && args,
                                              tuple_indices__<I...>)
    RETURNS(forward<Function>(f)(get<I>(forward<Tuple>(args))...))
  template <class Function, class Tuple>
  constexpr inline auto apply_to_tuple(Function && f,
                                       Tuple && args)
    RETURNS(apply_to_tuple_impl__(forward<Function>(f), forward<Tuple>(args),
      typename make_tuple_indices__<tuple_size<Tuple>::value>::type()))
} // end namespace util

// ===========================================================================
// Expression
// ===========================================================================

// This class marks the nested type as a function, if the nested type is a
// temporary object it store a copy, instead a reference.
// The second template parameter is used to define the type of storage (copy
// or reference).
template <class Expression, class> struct function;

template <class T, class U>
struct function {
  // the nested value
  U nested;

  // constructor
  template <class Arg>
  inline explicit function(Arg && value)
    : nested(util::forward<Arg>(value)) {}

  // forwards call to nested object
  template <class... Args>
  inline auto operator()(Args &&... args) const
    RETURNS(nested(util::forward<Args>(args)...))
};

// checks if is a function class
template <class T>
struct is_function : util::false_ {};
template <class T, class U>
struct is_function< function<T,U> > : util::true_ {};
template <class T, class U>
struct is_function< function<T,U> const > : util::true_ {};

// dispatch the correct type of function
template <class T>
struct make_function_type__;

// if is a reference, then store a reference of same type
template <class T>
struct make_function_type__<T &>
  { typedef function<typename util::remove_cv<T>::type, T &> type; };

// if is a temporary, then store a copy
template <class T>
struct make_function_type__<T &&>
  { typedef function<T, T> type; };

// make a function implementation
template <class T,
          bool = is_function<typename util::decay<T>::type>::value>
struct make_function__ {
  static inline auto call(T && t)
    RETURNS(typename make_function_type__<T &&>::type(util::forward<T>(t)))
};

template <class T>
struct make_function__<T,true> {
  static inline auto call(T && t)
    RETURNS(util::forward<T>(t))
};

// constructs a function from an expression, use this function instead of
// instantiate function objects
template <class T>
inline auto make_function(T && t)
  RETURNS(make_function__<T>::call(util::forward<T>(t)))

// remove the function
template <class T, class U>
inline U & remove_function(function<T,U> & f)
  { return(f.nested); }
template <class T, class U>
inline U const & remove_function(function<T,U> const & f)
  { return(f.nested); }
template <class T, class U>
inline auto remove_function(function<T,U> && f)
  RETURNS(util::forward<U>(f.nested))
template <class T>
inline auto remove_function(T && f)
  RETURNS(util::forward<T>(f))

// extracts the nth argument from a variadic list of arguments
namespace util {
  template <int N>
  struct get_nth_args {
    template <class... Args>
    static inline auto call(Args &&... args)
      RETURNS(get<N>(forward_as_tuple(forward<Args>(args)...)))
  };
} // end namespace util

// arguments
template <int N>
struct arg {
  static_assert(N >= 0, "please, specify a non negative number");

  // call
  template <class... Args>
  inline auto operator()(Args &&... args) const
    RETURNS(util::get_nth_args<N>::call(util::forward<Args>(args)...))
};

// constructs an argument from an integer
template <int N>
inline auto make_arg()
  RETURNS(make_function(arg<N>()))

// some usefull placeholders
namespace placeholders {
  const auto _x = make_arg<0>();
  const auto _y = make_arg<1>();
  const auto _z = make_arg<2>();
} // end namespace placeholders

// constant function
template <class Type>
struct constant {
  // the value of functions, it's stored always as a copy
  typename util::add_const<Type>::type value;

  // constructors
  template <class Arg>
  inline constant(Arg && arg)
    : value(util::forward<Arg>(arg)) {}

  // call
  template <class... Args>
  inline auto operator()(Args &&...) const
    RETURNS(value)
};

// checks if a type is a constant function
template <class T> struct is_constant : util::false_ {};
template <class T> struct is_constant< constant<T> > : util::true_ {};

// constructs a constant function from a value
template <class Arg>
inline auto make_constant(Arg && arg)
  RETURNS(make_function(constant<typename util::decay<Arg>::type
                                >(util::forward<Arg>(arg))))

// some special constants
#define BAG_SPECIAL_CONSTANT(Name, Value)                                    \
  struct Name {                                                              \
    template <class... Args>                                                 \
    inline auto operator()(Args &&...) const                                 \
      RETURNS(static_cast<BAG_DEFAULT_TYPE>(Value))                          \
  };                                                                         \
  template <> struct is_constant<Name> : util::true_ {}                      \
/**/

BAG_SPECIAL_CONSTANT(zero, 0);
BAG_SPECIAL_CONSTANT(one, 1);
BAG_SPECIAL_CONSTANT(pi, M_PI);

namespace constants {
  const auto _0 = make_function(zero());
  const auto _1 = make_function(one());
  const auto _pi = make_function(pi());
} // end namespace constants

namespace util {
  template <int I>
  inline auto make_tuple_indices()
    RETURNS(typename make_tuple_indices__<I>::type())

  template <class Function, class Operands, int... I, class... Args>
  inline auto expression_call(Function const & f,
                              Operands const & ops,
                              tuple_indices__<I...> const &,
                              Args &&... args)
    RETURNS(f(get<I>(ops)(forward<Args>(args)...)...))
} // end namespace util

// a node of evaluation tree
template <class Function, class Operands, class NestedOperands>
struct expression {
  static constexpr int arity = util::tuple_size<Operands>::value;

  typename util::add_const<Function>::type function;
  NestedOperands operands;

  // constructors
  template <class... Args>
  inline expression(Function const & func, Args &&... args)
    : function(func)
    , operands(util::forward<Args>(args)...) {}

  // call
  template <class... Args>
  inline auto operator()(Args &&... args) const
    RETURNS(expression_call(function, operands,
        util::make_tuple_indices<arity>(), util::forward<Args>(args)...))
};

// computes the correct type for an expression, choosing also the correct type
// of storage for each operands
template <class F, class... Ops>
struct make_expression_type__ {
  typedef F func_;
  typedef util::tuple<typename util::decay<Ops>::type...> ops_;
  typedef util::tuple<decltype(make_function(util::declval<Ops>()))...> nst_;

  typedef expression<func_,ops_,nst_> type;
};

// constructs a raw expression
template <class Function, class... Operands>
inline auto make_expression__(Function const & func, Operands &&... ops)
  RETURNS(typename make_expression_type__<Function,Operands &&...>::type(
    func, util::forward<Operands>(ops)...))

// an expression is nested inside a function
template <class Function, class... Operands>
inline auto make_expression(Function const & func, Operands &&... ops)
  RETURNS(make_function(make_expression__(
    func, remove_function(util::forward<Operands>(ops))...)))

// extracts the Ith operand
template <int I, class E>
inline auto operand(E && e)
  RETURNS(make_function(util::get<I>(
    remove_function(util::forward<E>(e)).operands))
  )

#define BAG_DEFINE_CPP_UNARY_OPERATOR(Operator, Name)                        \
  struct Name {                                                              \
    template <class Arg>                                                     \
    inline auto operator()(Arg && arg) const                                 \
      RETURNS(Operator util::forward<Arg>(arg))                              \
  };                                                                         \
  template <class E, class N>                                                \
  inline auto operator Operator(function<E,N> & f)                           \
    RETURNS(make_expression(Name(), f))                                      \
  template <class E, class N>                                                \
  inline auto operator Operator(function<E,N> const & f)                     \
    RETURNS(make_expression(Name(), f))                                      \
  template <class E, class N>                                                \
  inline auto operator Operator(function<E,N> && f)                          \
    RETURNS(make_expression(Name(), util::move(f)))                          \
/**/

template <class T, bool = is_function<T>::value>
struct forward_if_function_impl__ {
  template <class F>
  static inline auto call(F && f)
    RETURNS(util::forward<F>(f))
};

template <class T>
struct forward_if_function_impl__<T,false> {
  template <class F>
  static inline auto call(F && f)
    RETURNS(make_constant(util::forward<F>(f)))
};

template <class F>
inline auto forward_if_function(F && f)
  RETURNS(forward_if_function_impl__<typename util::decay<F>::type
                                    >::call(util::forward<F>(f)))


#define BAG_DEFINE_CPP_BINARY_OPERATOR(Operator, Name)                       \
  struct Name {                                                              \
    template <class Arg0, class Arg1>                                        \
    inline auto operator()(Arg0 && arg0, Arg1 && arg1) const                 \
      RETURNS(util::forward<Arg0>(arg0) Operator util::forward<Arg1>(arg1))  \
  };                                                                         \
  template <class E, class N, class T>                                       \
  inline auto operator Operator(function<E,N> & f, T && v)                   \
    RETURNS(make_expression(Name(), f,                                       \
      forward_if_function(util::forward<T>(v))))                             \
  template <class E, class N, class T>                                       \
  inline auto operator Operator(function<E,N> const & f, T && v)             \
    RETURNS(make_expression(Name(), f,                                       \
      forward_if_function(util::forward<T>(v))))                             \
  template <class E, class N, class T>                                       \
  inline auto operator Operator(function<E,N> && f, T && v)                  \
    RETURNS(make_expression(Name(), util::move(f),                           \
      forward_if_function(util::forward<T>(v))))                             \
  template <class T, class E, class N>                                       \
  inline auto operator Operator(T && v, function<E,N> & f)                   \
    RETURNS_IF(                                                              \
      (!is_function<typename util::decay<T>::type>::value),                  \
      make_expression(Name(), forward_if_function(util::forward<T>(v)), f))  \
  template <class T, class E, class N>                                       \
  inline auto operator Operator(T && v, function<E,N> const & f)             \
    RETURNS_IF(                                                              \
      (!is_function<typename util::decay<T>::type>::value),                  \
      make_expression(Name(), forward_if_function(util::forward<T>(v)), f))  \
  template <class T, class E, class N>                                       \
  inline auto operator Operator(T && v, function<E,N> && f)                  \
    RETURNS_IF(                                                              \
      (!is_function<typename util::decay<T>::type>::value),                  \
      make_expression(Name(), forward_if_function(util::forward<T>(v)),      \
        util::move(f)))                                                      \
/**/

#define BAG_DEFINE_FUNCTION(Name, Body)                                      \
  struct BAG_CAT(Name,_t) {                                                  \
    template <class Args>                                                    \
    static inline auto call(Args && args)                                    \
      RETURNS Body                                                           \
    template <class... Args>                                                 \
    inline auto operator()(Args &&... args) const                            \
      RETURNS(call(util::forward_as_tuple(util::forward<Args>(args)...)))    \
  };                                                                         \
  template <class... Args>                                                   \
  inline auto Name(Args &&... args)                                          \
    RETURNS(make_expression(BAG_CAT(Name,_t)(),                              \
      forward_if_function(util::forward<Args>(args))...))                    \
/**/

#define BAG_DEFINE_CMATH_FUNCTION(Name)                                      \
  struct BAG_CAT(Name,_t) {                                                  \
    template <class... Args>                                                 \
    inline auto operator()(Args &&... args) const                            \
      RETURNS(std::Name(util::forward<Args>(args)...))                       \
  };                                                                         \
  template <class... Args>                                                   \
  inline auto Name(Args &&... args)                                          \
    RETURNS(make_expression(BAG_CAT(Name,_t)(),                              \
      forward_if_function(util::forward<Args>(args))...))                    \
/**/

// arithmetic
BAG_DEFINE_CPP_UNARY_OPERATOR(+, unary_plus)
BAG_DEFINE_CPP_UNARY_OPERATOR(-, unary_minus)
BAG_DEFINE_CPP_BINARY_OPERATOR(+, plus)
BAG_DEFINE_CPP_BINARY_OPERATOR(-, minus)
BAG_DEFINE_CPP_BINARY_OPERATOR(*, times)
BAG_DEFINE_CPP_BINARY_OPERATOR(/, divides)
BAG_DEFINE_CPP_BINARY_OPERATOR(%, modulus)

// comparison
BAG_DEFINE_CPP_BINARY_OPERATOR(<, less)
BAG_DEFINE_CPP_BINARY_OPERATOR(<=, less_equal)
BAG_DEFINE_CPP_BINARY_OPERATOR(>, greater)
BAG_DEFINE_CPP_BINARY_OPERATOR(>=, greater_equal)
BAG_DEFINE_CPP_BINARY_OPERATOR(==, equal_to)
BAG_DEFINE_CPP_BINARY_OPERATOR(!=, not_equal_to)

// logical
BAG_DEFINE_CPP_BINARY_OPERATOR(&&, and_)
BAG_DEFINE_CPP_BINARY_OPERATOR(||, or_)
BAG_DEFINE_CPP_UNARY_OPERATOR(!, not_)

// bitwise
BAG_DEFINE_CPP_BINARY_OPERATOR(&, bitand_)
BAG_DEFINE_CPP_BINARY_OPERATOR(|, bitor_)
BAG_DEFINE_CPP_BINARY_OPERATOR(^, bitxor_)
BAG_DEFINE_CPP_BINARY_OPERATOR(<<, shift_left)
BAG_DEFINE_CPP_BINARY_OPERATOR(>>, shift_right)

#ifndef BAG_DONT_USE_CMATH
// basic
BAG_DEFINE_CMATH_FUNCTION(abs)
// BAG_DEFINE_CMATH_FUNCTION(labs)
// BAG_DEFINE_CMATH_FUNCTION(llabs)
// BAG_DEFINE_CMATH_FUNCTION(imaxabs)
BAG_DEFINE_CMATH_FUNCTION(fabs)
// BAG_DEFINE_CMATH_FUNCTION(div)
// BAG_DEFINE_CMATH_FUNCTION(ldiv)
// BAG_DEFINE_CMATH_FUNCTION(lldiv)
// BAG_DEFINE_CMATH_FUNCTION(imaxdiv)
BAG_DEFINE_CMATH_FUNCTION(fmod)
BAG_DEFINE_CMATH_FUNCTION(remainder)
BAG_DEFINE_CMATH_FUNCTION(remquo)
BAG_DEFINE_CMATH_FUNCTION(fma)
BAG_DEFINE_CMATH_FUNCTION(fmax)
// BAG_DEFINE_CMATH_FUNCTION(fmim)
BAG_DEFINE_CMATH_FUNCTION(fdim)
BAG_DEFINE_CMATH_FUNCTION(nan)
BAG_DEFINE_CMATH_FUNCTION(nanf)
BAG_DEFINE_CMATH_FUNCTION(nanl)

// exponential
BAG_DEFINE_CMATH_FUNCTION(exp)
BAG_DEFINE_CMATH_FUNCTION(exp2)
BAG_DEFINE_CMATH_FUNCTION(expm1)
BAG_DEFINE_CMATH_FUNCTION(log)
BAG_DEFINE_CMATH_FUNCTION(log10)
BAG_DEFINE_CMATH_FUNCTION(log1p)
BAG_DEFINE_CMATH_FUNCTION(log2)

// power
BAG_DEFINE_CMATH_FUNCTION(sqrt)
BAG_DEFINE_CMATH_FUNCTION(cbrt)
BAG_DEFINE_CMATH_FUNCTION(hypot)
BAG_DEFINE_CMATH_FUNCTION(pow)

// trigonometric
BAG_DEFINE_CMATH_FUNCTION(cos)
BAG_DEFINE_CMATH_FUNCTION(sin)
BAG_DEFINE_CMATH_FUNCTION(tan)
BAG_DEFINE_CMATH_FUNCTION(acos)
BAG_DEFINE_CMATH_FUNCTION(asin)
BAG_DEFINE_CMATH_FUNCTION(atan)
BAG_DEFINE_CMATH_FUNCTION(atan2)

// hyperbolic
BAG_DEFINE_CMATH_FUNCTION(cosh)
BAG_DEFINE_CMATH_FUNCTION(sinh)
BAG_DEFINE_CMATH_FUNCTION(tanh)
BAG_DEFINE_CMATH_FUNCTION(acosh)
BAG_DEFINE_CMATH_FUNCTION(asinh)
BAG_DEFINE_CMATH_FUNCTION(atanh)

// error
BAG_DEFINE_CMATH_FUNCTION(erf)
BAG_DEFINE_CMATH_FUNCTION(erfc)
BAG_DEFINE_CMATH_FUNCTION(lgamma)
BAG_DEFINE_CMATH_FUNCTION(tgamma)

// round
BAG_DEFINE_CMATH_FUNCTION(ceil)
BAG_DEFINE_CMATH_FUNCTION(floor)
BAG_DEFINE_CMATH_FUNCTION(trunc)
BAG_DEFINE_CMATH_FUNCTION(round)
BAG_DEFINE_CMATH_FUNCTION(lround)
BAG_DEFINE_CMATH_FUNCTION(llround)
BAG_DEFINE_CMATH_FUNCTION(nearbyint)
BAG_DEFINE_CMATH_FUNCTION(rint)
BAG_DEFINE_CMATH_FUNCTION(lrint)
BAG_DEFINE_CMATH_FUNCTION(llrint)

// floating point
BAG_DEFINE_CMATH_FUNCTION(frexp)
BAG_DEFINE_CMATH_FUNCTION(ldexp)
BAG_DEFINE_CMATH_FUNCTION(modf)
BAG_DEFINE_CMATH_FUNCTION(scalbn)
BAG_DEFINE_CMATH_FUNCTION(scalbln)
BAG_DEFINE_CMATH_FUNCTION(ilogb)
BAG_DEFINE_CMATH_FUNCTION(logb)
BAG_DEFINE_CMATH_FUNCTION(nextafter)
BAG_DEFINE_CMATH_FUNCTION(nexttoward)
BAG_DEFINE_CMATH_FUNCTION(copysign)

// classification
BAG_DEFINE_CMATH_FUNCTION(fpclassify)
BAG_DEFINE_CMATH_FUNCTION(isfinite)
BAG_DEFINE_CMATH_FUNCTION(isinf)
BAG_DEFINE_CMATH_FUNCTION(isnan)
BAG_DEFINE_CMATH_FUNCTION(isnormal)
BAG_DEFINE_CMATH_FUNCTION(signbit)
#endif // BAG_DONT_USE_CMATH

// if
BAG_DEFINE_FUNCTION(if_,
  (util::get<0>(args) ? util::get<1>(args) : util::get<2>(args)) )

// min and max
BAG_DEFINE_FUNCTION(min, (util::min(util::get<0>(args), util::get<1>(args))))
BAG_DEFINE_FUNCTION(max, (util::max(util::get<0>(args), util::get<1>(args))))

// ===========================================================================
// Optimization
// ===========================================================================

// empty rule
template <class Expr>
struct optimization_rule {
  template <class T>
  static inline auto call(T && t)
    RETURNS(util::forward<T>(t))
};

#define BAG_OPTIMIZATION_RULE(Template, Function, Optimized)                 \
  template < BAG_TUPLE_REM(Template) >                                       \
  struct optimization_rule< BAG_TUPLE_REM(Function) > {                      \
    template <class Expr>                                                    \
    static inline auto call(Expr && expr)                                    \
      RETURNS(remove_function Optimized)                                     \
  };                                                                         \
/**/

// apply the rules to an expression
template <class Expr>
inline auto optimize_expression(Expr && expr)
  RETURNS(
    remove_function(
      optimization_rule<typename util::decay<Expr>::type
                       >::call(util::forward<Expr>(expr))
    )
  )

// optimization loop
template <class Expr, class... Previous>
struct optimization_loop {
  template <class T>
  static inline auto call(T && t)
    RETURNS(optimization_loop<
      typename util::decay<decltype(optimize_expression(util::declval<T>()))
                          >::type,
      Expr, Previous...>::call(optimize_expression(util::forward<T>(t)))
    )
};

template <class Expr, class... Others>
struct optimization_loop<Expr, Expr, Others...> {
  template <class T>
  static inline auto call(T && t)
    RETURNS(util::forward<T>(t))
};

template <class T>
inline auto optimize_impl__(T && t)
  RETURNS(optimization_loop<typename util::decay<T>::type
                           >::call(util::forward<T>(t)))

template <class Function>
inline auto optimize(Function && f)
  RETURNS(
    make_function(
      optimize_impl__(
        remove_function( util::forward<Function>(f) )
      )
    )
  )

namespace util {
  // check if all bool constant are true
  template <bool... Values> struct all__:true_{};
  template <bool... Values> struct all__<true,Values...>:all__<Values...>{};
  template <bool... Values> struct all__<false,Values...>:false_{};

  // check if all operands are constants
  template <class Operands> struct all_constants__;
  template <class... Operands>
  struct all_constants__< tuple<Operands...> >
    : all__<is_constant<Operands>::value...> {};
} //end namespace util

// dispatch the rule, depends on the fact that all nested operands are
// constants
template <bool> struct expression_rule_dispatch__;

template <>
struct expression_rule_dispatch__<false> {
  template <int... I, class Expr>
  static inline auto call(util::tuple_indices__<I...>, Expr && expr)
    RETURNS(
      make_expression(
        expr.function,
        optimize(operand<I>(util::forward<Expr>(expr)))...
      )
    )
};

template <>
struct expression_rule_dispatch__<true> {
  template <int... I, class Expr>
  static inline auto call(util::tuple_indices__<I...>, Expr && expr)
    RETURNS(
      make_constant(
        expr.function(operand<I>(util::forward<Expr>(expr))()...)
      )
    )
};

// recursive optimization of expression
template <class Operator, class Operands, class Nested>
struct optimization_rule< expression<Operator, Operands, Nested> > {
  static constexpr int arity = util::tuple_size<Operands>::value;

  template <class Expr>
  static inline auto call(Expr && expr)
    RETURNS(
      expression_rule_dispatch__<util::all_constants__<Operands>::value
                                >::call(
        typename util::make_tuple_indices__<arity>::type(),
        util::forward<Expr>(expr)
      )
    )
};

// plus zero
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<plus, util::tuple<zero,T>, E>),
  (operand<1>(util::forward<Expr>(expr)))
)
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<plus, util::tuple<T,zero>, E>),
  (operand<0>(util::forward<Expr>(expr)))
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<plus, util::tuple<zero,zero>, E>),
  (constants::_0)
)
// minus zero
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<minus, util::tuple<zero,T>, E>),
  (-operand<1>(util::forward<Expr>(expr)))
)
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<minus, util::tuple<T,zero>, E>),
  (operand<0>(util::forward<Expr>(expr)))
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<minus, util::tuple<zero,zero>, E>),
  (constants::_0)
)
// times zero
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<times, util::tuple<zero,T>, E>),
  (constants::_0)
)
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<times, util::tuple<T,zero>, E>),
  (constants::_0)
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<times, util::tuple<zero,zero>,E>),
  (constants::_0)
)
// times one
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<times, util::tuple<one,T>, E>),
  (operand<1>(util::forward<Expr>(expr)))
)
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<times, util::tuple<T,one>, E>),
  (operand<0>(util::forward<Expr>(expr)))
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<times, util::tuple<one,one>, E>),
  (constants::_1)
)
// divides zero
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<divides, util::tuple<zero,T>, E>),
  (constants::_0)
)
// divides one
BAG_OPTIMIZATION_RULE(
  (class T, class E),
  (expression<divides, util::tuple<T,one>, E>),
  (operand<0>(util::forward<Expr>(expr)))
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<divides, util::tuple<one,one>, E>),
  (constants::_1)
)
// cancellation
//BAG_OPTIMIZATION_RULE(
//  (class E),
//  (expression<minus, util::tuple<zero,zero>, E>),
//  (constants::_0)
//)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<minus, util::tuple<one,one>, E>),
  (constants::_0)
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<minus, util::tuple<pi,pi>, E>),
  (constants::_0)
)
// trigonometric
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<cos_t, util::tuple<zero>, E>),
  (constants::_1)
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<cos_t, util::tuple<pi>, E>),
  (-constants::_1)
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<sin_t, util::tuple<zero>, E>),
  (constants::_0)
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<sin_t, util::tuple<pi>, E>),
  (constants::_0)
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<tan_t, util::tuple<zero>, E>),
  (constants::_0)
)
BAG_OPTIMIZATION_RULE(
  (class E),
  (expression<tan_t, util::tuple<pi>, E>),
  (constants::_0)
)

// ===========================================================================
// Derivative
// ===========================================================================

template <int N, class T> struct derivative_rule;

// extract the indices of an argument, removing the sorrounding function
template <class T>
struct variable_indices;
template <class T, class U>
struct variable_indices< function<T,U> >
  : variable_indices<T> {};
template <int N>
struct variable_indices< arg<N> > {
  static constexpr int value = N;
};

// implement the derivative, calling the rules
template <int N, class T>
inline auto D_impl__(T && t)
  RETURNS(
    make_function(
      derivative_rule<N,typename util::decay<T>::type
                     >::call(util::forward<T>(t))
    )
  )

// forward the function to the implementation
template <class Function, class Variable>
inline auto D(Function && f, Variable && v)
  RETURNS(
    optimize(
      D_impl__<variable_indices<typename util::decay<Variable>::type>::value>(
        remove_function(optimize(util::forward<Function>(f)))
      )
    )
  )

#define BAG_DERIVATIVE_RULE(Function, Derivative)                            \
  template <int N>                                                           \
  struct derivative_rule< N, BAG_TUPLE_REM(Function) > {                     \
    template <class Expr>                                                    \
    static inline auto D(Expr && expr)                                       \
      RETURNS(D_impl__<N>(remove_function(util::forward<Expr>(expr))))       \
    template <class Expr>                                                    \
    static inline auto call(Expr && expr)                                    \
      RETURNS(remove_function Derivative)                                    \
  };                                                                         \
/**/
#define BAG_DERIVATIVE_RULE_T(Template, Function, Derivative)                \
  template <int N, BAG_TUPLE_REM(Template) >                                 \
  struct derivative_rule< N, BAG_TUPLE_REM(Function) > {                     \
    template <class Expr>                                                    \
    static inline auto D(Expr && expr)                                       \
      RETURNS(D_impl__<N>(remove_function(util::forward<Expr>(expr))))       \
    template <class Expr>                                                    \
    static inline auto call(Expr && expr)                                    \
      RETURNS(remove_function Derivative)                                    \
  };                                                                         \
/**/

// arguments
BAG_DERIVATIVE_RULE((arg<N>), (constants::_1))
BAG_DERIVATIVE_RULE_T((int M), (arg<M>), (constants::_0))

// constants
BAG_DERIVATIVE_RULE_T((class T), (constant<T>), (constants::_0))
BAG_DERIVATIVE_RULE((zero), (constants::_0))
BAG_DERIVATIVE_RULE((one), (constants::_0))
BAG_DERIVATIVE_RULE((pi), (constants::_0))

// unary
BAG_DERIVATIVE_RULE_T(
  (class L, class E),
  (expression<unary_plus, util::tuple<L>, E>),
  (+ D(operand<0>(util::forward<Expr>(expr))))
)
BAG_DERIVATIVE_RULE_T(
  (class L, class E),
  (expression<unary_minus, util::tuple<L>, E>),
  (- D(operand<0>(util::forward<Expr>(expr))))
)

// algebraic
BAG_DERIVATIVE_RULE_T(
  (class L, class R, class E),
  (expression<plus, util::tuple<L,R>, E>),
  (D(operand<0>(util::forward<Expr>(expr))) +
   D(operand<1>(util::forward<Expr>(expr))))
)
BAG_DERIVATIVE_RULE_T(
  (class L, class R, class E),
  (expression<minus, util::tuple<L,R>, E>),
  (D(operand<0>(util::forward<Expr>(expr))) -
   D(operand<1>(util::forward<Expr>(expr))))
)
BAG_DERIVATIVE_RULE_T(
  (class L, class R, class E),
  (expression<times, util::tuple<L,R>, E>),
  (D(operand<0>(util::forward<Expr>(expr))) * 
     operand<1>(util::forward<Expr>(expr)) +
     operand<0>(util::forward<Expr>(expr)) *
   D(operand<1>(util::forward<Expr>(expr))))
)

BAG_END_NAMESPACE

#endif // BAG_HPP
// vim: set filetype=cpp11 :
