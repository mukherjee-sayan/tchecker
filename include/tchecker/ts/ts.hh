/*
 * This file is a part of the TChecker project.
 *
 * See files AUTHORS and LICENSE for copyright details.
 *
 */

#ifndef TCHECKER_TS_HH
#define TCHECKER_TS_HH

#include <tuple>
#include <type_traits>
#include <vector>

#include "tchecker/basictypes.hh"
#include "tchecker/ts/state.hh"
#include "tchecker/ts/transition.hh"
#include "tchecker/utils/iterator.hh"

/*!
 \file ts.hh
 \brief Interface to transition system
 */

namespace tchecker {

namespace ts {

/*!
 \class ts_t
 \brief Transition system
 \tparam STATE : type of state
 \tparam CONST_STATE : type of const state
 \tparam TRANSITION : type of transition
 \tparam INITIAL_RANGE : type of range of initial states, should be tchecker::make_range_t<...>
 \tparam OUTGOING_EDGES_RANGE : type of range of outgoing edges, should be tchecker::make_range_t<...>
 \tparam INITIAL_VALUE : type of value in INITIAL_RANGE
 \tparam OUTGOING_EDGES_VALUE : type of value in OUTGOING_EDGES_RANGE
 */
template <class STATE, class CONST_STATE, class TRANSITION, class INITIAL_RANGE, class OUTGOING_EDGES_RANGE,
          class INITIAL_VALUE = typename std::iterator_traits<typename INITIAL_RANGE::begin_iterator_t>::reference_type const,
          class OUTGOING_EDGES_VALUE =
              typename std::iterator_traits<typename OUTGOING_EDGES_RANGE::begin_iterator_t>::reference_type const>
class ts_t {
public:
  /*!
   \brief Type of state
   */
  using state_t = STATE;

  /*!
  \brief Type of const state
  */
  using const_state_t = CONST_STATE;

  /*!
   \brief Type of transition
   */
  using transition_t = TRANSITION;

  /*!
   \brief Type of range of initial states
   */
  using initial_range_t = INITIAL_RANGE;

  /*!
   \brief Value type for range over initial states
   */
  using initial_value_t = INITIAL_VALUE;

  /*!
   \brief Type of range over outgoing edges
   */
  using outgoing_edges_range_t = OUTGOING_EDGES_RANGE;

  /*!
   \brief Value type for range of outgoing edges
   */
  using outgoing_edges_value_t = OUTGOING_EDGES_VALUE;

  /*!
  \brief Type of tuples (status, state, transition)
  */
  using sst_t = std::tuple<enum tchecker::state_status_t, STATE, TRANSITION>;

  /*!
   \brief Destructor
   */
  virtual ~ts_t() = default;

  /*!
   \brief Accessor
   \return Initial edges
   */
  virtual INITIAL_RANGE initial_edges() = 0;

  /*!
   \brief Initial state and transition
   \param v : initial state valuation
   \post state s and transition t have been initialized from v
   \return (status, s, t) where initial state s and initial transition t have
   been computed from v, and status is the status of state s after initialization
   \note t represents an initial transition to s
   */
  virtual std::tuple<enum tchecker::state_status_t, STATE, TRANSITION> initial(INITIAL_VALUE const & v) = 0;

  /*!
   \brief Accessor
   \param s : state
   \return outgoing edges from state s
   */
  virtual OUTGOING_EDGES_RANGE outgoing_edges(CONST_STATE const & s) = 0;

  /*!
   \brief Next state and transition
   \param s : state
   \param v : outgoing edge value
   \return (status, s', t) where next state s' and transition t have been
   computed from v, and status is the status of state s'
   */
  virtual std::tuple<enum tchecker::state_status_t, STATE, TRANSITION> next(CONST_STATE const & s,
                                                                            OUTGOING_EDGES_VALUE const & v) = 0;

  /*!
  \brief Initial states and transitions with selected status
  \param v : container
  \param mask : mask on initial states
  \post all tuples (status, s, t) of status, initial states and transitions such
  that status matches mask (i.e. status & mask != 0) have been pushed back into v
   */
  virtual void initial(std::vector<sst_t> & v, enum tchecker::state_status_t mask)
  {
    enum tchecker::state_status_t status;
    STATE state;
    TRANSITION transition;
    INITIAL_RANGE edges = initial_edges();
    for (INITIAL_VALUE && edge : edges) {
      std::tie(status, state, transition) = initial(edge);
      if (status & mask)
        v.push_back(std::make_tuple(status, state, transition));
    }
  }

  /*!
  \brief Next states and transitions with selected status
  \param s : state
  \param v : container
  \param mask : mask on next states
  \post all tuples (status, s', t) such that s -t-> s' is a transition and the
  status of s' matches mask (i.e. status & mask != 0) have been pushed to v
  */
  virtual void next(CONST_STATE const & s, std::vector<sst_t> & v, enum tchecker::state_status_t mask)
  {
    enum tchecker::state_status_t status;
    STATE next_state;
    TRANSITION transition;
    OUTGOING_EDGES_RANGE edges = outgoing_edges(s);
    for (OUTGOING_EDGES_VALUE && edge : edges) {
      std::tie(status, next_state, transition) = next(s, edge);
      if (status & mask)
        v.push_back(std::make_tuple(status, next_state, transition));
    }
  }
};

} // end of namespace ts

} // end of namespace tchecker

#endif // TCHECKER_TS_HH
