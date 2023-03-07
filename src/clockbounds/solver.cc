/*
 * This file is a part of the TChecker project.
 *
 * See files AUTHORS and LICENSE for copyright details.
 *
 */

#include <cassert>
#include <cstring>
#include <unordered_set>

#include "tchecker/clockbounds/solver.hh"
#include "tchecker/expression/static_analysis.hh"

namespace tchecker {

namespace clockbounds {

df_solver_t::df_solver_t(tchecker::ta::system_t const & system)
    : _loc_number(system.locations_count()), _clock_number(system.clock_variables().size(tchecker::VK_FLATTENED)),
      _loc_pid(_loc_number, 0),
      _dim(1 + _loc_number * _clock_number), // 1 variable for each clock in each location, plus 1 for dummy clock 0
      _L(nullptr), _U(nullptr), _has_solution(true)
{
  if ((_loc_number > 0) && (_clock_number > 0) && ((_dim < _loc_number) || (_dim < _clock_number)))
    throw std::invalid_argument("invalid number of clocks or locations (overflow)");

  for (tchecker::loc_id_t id = 0; id < _loc_number; ++id)
    _loc_pid[id] = system.location(id)->pid();

  _L = new tchecker::dbm::db_t[_dim * _dim];
  _U = new tchecker::dbm::db_t[_dim * _dim];
  clear();
}

df_solver_t::df_solver_t(tchecker::clockbounds::df_solver_t const & solver)
    : _loc_number(solver._loc_number), _clock_number(solver._clock_number), _loc_pid(solver._loc_pid), _dim(solver._dim),
      _L(nullptr), _U(nullptr), _has_solution(true)
{
  _L = new tchecker::dbm::db_t[_dim * _dim];
  _U = new tchecker::dbm::db_t[_dim * _dim];
  memcpy(_L, solver._L, _dim * _dim * sizeof(*_L));
  memcpy(_U, solver._U, _dim * _dim * sizeof(*_U));
}

df_solver_t::df_solver_t(tchecker::clockbounds::df_solver_t && solver)
    : _loc_number(std::move(solver._loc_number)), _clock_number(std::move(solver._clock_number)),
      _loc_pid(std::move(solver._loc_pid)), _dim(std::move(solver._dim)), _L(std::move(solver._L)), _U(std::move(solver._U)),
      _has_solution(std::move(solver._has_solution))
{
  solver._loc_number = 0;
  solver._clock_number = 0;
  solver._dim = 1;
  solver._L = nullptr;
  solver._U = nullptr;
  solver._has_solution = false;
}

df_solver_t::~df_solver_t()
{
  delete[] _L;
  delete[] _U;
}

tchecker::clockbounds::df_solver_t & df_solver_t::operator=(tchecker::clockbounds::df_solver_t const & solver)
{
  if (this != &solver) {
    _loc_number = solver._loc_number;
    _clock_number = solver._clock_number;
    _loc_pid = solver._loc_pid;
    _dim = solver._dim;

    delete[] _L;
    _L = new tchecker::dbm::db_t[_dim * _dim];
    memcpy(_L, solver._L, _dim * _dim * sizeof(*_L));

    delete[] _U;
    _U = new tchecker::dbm::db_t[_dim * _dim];
    memcpy(_U, solver._U, _dim * _dim * sizeof(*_U));

    _has_solution = solver._has_solution;
  }

  return *this;
}

tchecker::clockbounds::df_solver_t & df_solver_t::operator=(tchecker::clockbounds::df_solver_t && solver)
{
  if (this != &solver) {
    _loc_number = std::move(solver._loc_number);
    _clock_number = std::move(solver._clock_number);
    _loc_pid = std::move(solver._loc_pid);
    _dim = std::move(solver._dim);
    _L = std::move(solver._L);
    _U = std::move(solver._U);
    _has_solution = std::move(solver._has_solution);

    solver._loc_number = 0;
    solver._clock_number = 0;
    solver._dim = 1;
    solver._L = nullptr;
    solver._U = nullptr;
    solver._has_solution = false;
  }

  return *this;
}

tchecker::clock_id_t df_solver_t::clock_number() const { return _clock_number; }

tchecker::clock_id_t df_solver_t::loc_number() const { return _loc_number; }

tchecker::clockbounds::bound_t df_solver_t::L(tchecker::loc_id_t l, tchecker::clock_id_t x) const
{
  assert(l < _loc_number);
  assert(x < _clock_number);
  tchecker::dbm::db_t db = _L[0 * _dim + index(l, x)];
  return (db == tchecker::dbm::LT_INFINITY ? tchecker::clockbounds::NO_BOUND : -tchecker::dbm::value(db));
}

tchecker::clockbounds::bound_t df_solver_t::U(tchecker::loc_id_t l, tchecker::clock_id_t x) const
{
  assert(l < _loc_number);
  assert(x < _clock_number);
  tchecker::dbm::db_t db = _U[0 * _dim + index(l, x)];
  return (db == tchecker::dbm::LT_INFINITY ? tchecker::clockbounds::NO_BOUND : -tchecker::dbm::value(db));
}

bool df_solver_t::has_solution() const { return _has_solution; }

void df_solver_t::clear()
{
  // <inf everywhere except <=0 on diagonal
  for (tchecker::clock_id_t x = 0; x < _dim; ++x) {
    for (tchecker::clock_id_t y = 0; y < _dim; ++y) {
      _L[x * _dim + y] = tchecker::dbm::LT_INFINITY;
      _U[x * _dim + y] = tchecker::dbm::LT_INFINITY;
    }
    _L[x * _dim + x] = tchecker::dbm::LE_ZERO;
    _U[x * _dim + x] = tchecker::dbm::LE_ZERO;
  }

  _has_solution = true;
}

void df_solver_t::add_lower_bound_guard(tchecker::loc_id_t l, tchecker::clock_id_t x, tchecker::integer_t c)
{
  assert(l < _loc_number);
  assert(x < _clock_number);
  // L_{l, x} >= c  (i.e. 0 - L_{l, x} <= -c)
  _has_solution &= (tchecker::dbm::constrain(_L, _dim, 0, index(l, x), tchecker::dbm::LE, -c) != tchecker::dbm::EMPTY);
}

void df_solver_t::add_upper_bound_guard(tchecker::loc_id_t l, tchecker::clock_id_t x, tchecker::integer_t c)
{
  assert(l < _loc_number);
  assert(x < _clock_number);
  // U_{l, x} >= c  (i.e. 0 - U_{l ,x} <= -c)
  _has_solution &= (tchecker::dbm::constrain(_U, _dim, 0, index(l, x), tchecker::dbm::LE, -c) != tchecker::dbm::EMPTY);
}

void df_solver_t::add_assignment(tchecker::loc_id_t l1, tchecker::loc_id_t l2, tchecker::clock_id_t x, tchecker::clock_id_t y,
                                 tchecker::integer_t c)
{
  assert(l1 < _loc_number);
  assert(l2 < _loc_number);
  assert(x < _clock_number);
  assert(y < _clock_number);
  // Propagation over the edge: L_{l2,x} - L_{l1,y} <= c / U_{l2,x} - U_{l1,xy} <= c
  _has_solution &=
      (tchecker::dbm::constrain(_L, _dim, index(l2, x), index(l1, y), tchecker::dbm::LE, c) != tchecker::dbm::EMPTY);
  _has_solution &=
      (tchecker::dbm::constrain(_U, _dim, index(l2, x), index(l1, y), tchecker::dbm::LE, c) != tchecker::dbm::EMPTY);

  // Propagation across processes: L_{m,x} - L_{l1,y} <= c / U_{m,x} - U_{l1,y} <= c
  // for every location m in another process
  for (tchecker::loc_id_t m = 0; m < _loc_number; ++m)
    if (_loc_pid[m] != _loc_pid[l1]) {
      _has_solution &=
          (tchecker::dbm::constrain(_L, _dim, index(m, x), index(l1, y), tchecker::dbm::LE, c) != tchecker::dbm::EMPTY);
      _has_solution &=
          (tchecker::dbm::constrain(_U, _dim, index(m, x), index(l1, y), tchecker::dbm::LE, c) != tchecker::dbm::EMPTY);
    }
}

void df_solver_t::add_no_assignement(tchecker::loc_id_t l1, tchecker::loc_id_t l2, tchecker::clock_id_t x)
{
  assert(l1 < _loc_number);
  assert(l2 < _loc_number);
  assert(x < _clock_number);
  // L_{l2,x} - L_{l1,x} <= 0
  _has_solution &=
      (tchecker::dbm::constrain(_L, _dim, index(l2, x), index(l1, x), tchecker::dbm::LE, 0) != tchecker::dbm::EMPTY);
  // U_{l2,x} - U_{l1,x} <= 0
  _has_solution &=
      (tchecker::dbm::constrain(_U, _dim, index(l2, x), index(l1, x), tchecker::dbm::LE, 0) != tchecker::dbm::EMPTY);
}

std::size_t df_solver_t::index(tchecker::loc_id_t l, tchecker::clock_id_t x) const
{
  assert(l < _loc_number);
  assert(x < _clock_number);
  return 1 + l * _clock_number + x;
}

/*!
\class df_solver_updater_t
\brief Update solver constraints from expressions and statements
\see tchecker::clockbounds::df_solver_t for constraints generated from expressions
*/
class df_solver_updater_t : public tchecker::typed_expression_visitor_t, public tchecker::typed_statement_visitor_t {
public:
  /*!
  \brief Constructor
  \param src : source location identifier
  \param tgt : target location identifier
  \param solver : a solver
  \note this updates constraints in solver for locations src and tgt
  */
  df_solver_updater_t(tchecker::loc_id_t src, tchecker::loc_id_t tgt,
                      std::shared_ptr<tchecker::clockbounds::df_solver_t> const & solver)
      : _src(src), _tgt(tgt), _solver(solver)
  {
  }

  /*!
  \brief Copy constructor
  \param updater : an updater
  \post this is a copy of updater
  */
  df_solver_updater_t(tchecker::clockbounds::df_solver_updater_t const & updater)
      : _src(updater._src), _tgt(updater._tgt), _solver(updater._solver)
  {
  }

  /*!
  \brief Move constructor
  \param updater : an updater
  \post updater has been moved to this
  */
  df_solver_updater_t(tchecker::clockbounds::df_solver_updater_t && updater)
      : _src(std::move(updater._src)), _tgt(std::move(updater._tgt)), _solver(std::move(updater._solver))
  {
  }

  /*!
  \brief Destructor
  */
  ~df_solver_updater_t() = default;

  /*!
  \brief Assignment operator
  \param updater : an updater
  \post this is a copy of updater
  \return this
  */
  tchecker::clockbounds::df_solver_updater_t & operator=(tchecker::clockbounds::df_solver_updater_t const & updater)
  {
    if (this != &updater) {
      _src = updater._src;
      _tgt = updater._tgt;
      _solver = updater._solver;
    }
    return *this;
  }

  /*!
  \brief Move assignment operator
  \param updater : an updater
  \post updater has been moved to this
  \return this
  */
  tchecker::clockbounds::df_solver_updater_t & operator=(tchecker::clockbounds::df_solver_updater_t && updater)
  {
    if (this != &updater) {
      _src = std::move(updater._src);
      _tgt = std::move(updater._tgt);
      _solver = std::move(updater._solver);
    }
    return *this;
  }

  /*!
  \brief Visitor
  \post left and right operand have been visited if expr is a logical-and expression
  */
  virtual void visit(tchecker::typed_binary_expression_t const & expr)
  {
    if (expr.binary_operator() == tchecker::EXPR_OP_LAND) {
      expr.left_operand().visit(*this);
      expr.right_operand().visit(*this);
    }
  }

  /*!
  \brief Visitor
  \post sub-expression has been visited
  */
  virtual void visit(tchecker::typed_par_expression_t const & expr) { expr.expr().visit(*this); }

  /*!
  \brief Visitor
  \post If expr is a lower-bound guard (x>c, x>=c, x==c), then a constraint on clock lower bounds has been added to
  _solver for every clock x (x could be an array) w.r.t. bound c (using method add_lower_bound_guard). If expr is
  an upper-bound guard (x<c, x<=c, x==c), then a constraint on clock upper bounds has been added to _solver for
  every clock x (x could be an array) w.r.t. bound c (using method add_upper_bound_guard).
  */
  virtual void visit(tchecker::typed_simple_clkconstr_expression_t const & expr)
  {
    tchecker::range_t<tchecker::clock_id_t> clocks = tchecker::extract_lvalue_variable_ids(expr.clock());
    tchecker::integer_t bound = tchecker::const_evaluate(expr.bound(), tchecker::clockbounds::MAX_BOUND);

    if ((expr.binary_operator() == tchecker::EXPR_OP_LT) || (expr.binary_operator() == tchecker::EXPR_OP_LE) ||
        (expr.binary_operator() == tchecker::EXPR_OP_EQ)) {
      for (tchecker::clock_id_t clock = clocks.begin(); clock != clocks.end(); ++clock)
        _solver->add_upper_bound_guard(_src, clock, bound);
    }

    if ((expr.binary_operator() == tchecker::EXPR_OP_GT) || (expr.binary_operator() == tchecker::EXPR_OP_GE) ||
        (expr.binary_operator() == tchecker::EXPR_OP_EQ)) {
      for (tchecker::clock_id_t clock = clocks.begin(); clock != clocks.end(); ++clock)
        _solver->add_lower_bound_guard(_src, clock, bound);
    }
  }

  /*!
  \brief Visitor
  \throw std::runtime_error : as diagonal constraints are not supported by diagonal-free solver
  */
  virtual void visit(tchecker::typed_diagonal_clkconstr_expression_t const & expr)
  {
    throw std::runtime_error("unsupported diagonal constraints");
  }

  // Other visitors on expressions
  virtual void visit(tchecker::typed_int_expression_t const &) {}
  virtual void visit(tchecker::typed_var_expression_t const &) {}
  virtual void visit(tchecker::typed_bounded_var_expression_t const &) {}
  virtual void visit(tchecker::typed_array_expression_t const &) {}
  virtual void visit(tchecker::typed_unary_expression_t const &) {}
  virtual void visit(tchecker::typed_ite_expression_t const &) {}

  /*!
  \brief Visitor
  \post first and second statements have been visited
  */
  virtual void visit(tchecker::typed_sequence_statement_t const & stmt)
  {
    stmt.first().visit(*this);
    stmt.second().visit(*this);
  }

  /*!
  \brief Visitor
  \post condition expression, then_stmt, else_stmt are visited
  */
  virtual void visit(tchecker::typed_if_statement_t const & stmt)
  {
    stmt.condition().visit(*this);
    stmt.then_stmt().visit(*this);
    stmt.else_stmt().visit(*this);
  }

  /*!
  \brief Visitor
  \post condition expression and stmt statement are visited
  */
  virtual void visit(tchecker::typed_while_statement_t const & stmt)
  {
    stmt.condition().visit(*this);
    stmt.statement().visit(*this);
  }

  /*!
  \brief Visitor
  \post No constraint generated for clock assignment x:=c
  */
  virtual void visit(tchecker::typed_int_to_clock_assign_statement_t const &) {}

  /*!
  \brief Visitor
  \post For assignment x:=y, a constraint for every clock x (x could be an array) and every clock y (y could be
  an array) has been added to _solver using method add_assignment
  */
  virtual void visit(tchecker::typed_clock_to_clock_assign_statement_t const & stmt)
  {
    tchecker::range_t<tchecker::clock_id_t> lclocks = tchecker::extract_lvalue_variable_ids(stmt.lclock());
    tchecker::range_t<tchecker::clock_id_t> rclocks = tchecker::extract_lvalue_variable_ids(stmt.rclock());

    for (tchecker::clock_id_t lclock = lclocks.begin(); lclock != lclocks.end(); ++lclock)
      for (tchecker::clock_id_t rclock = rclocks.begin(); rclock != rclocks.end(); ++rclock)
        _solver->add_assignment(_src, lclock, _tgt, rclock, 0);
  }

  /*!
  \brief Visitor
  \post For assignment x:=y+c, a constraint for every clock x (x could be an array) and every clock y (y could be
  an array) using value c has been added to _solver using method add_assignment
  */
  virtual void visit(tchecker::typed_sum_to_clock_assign_statement_t const & stmt)
  {
    tchecker::range_t<tchecker::clock_id_t> lclocks = tchecker::extract_lvalue_variable_ids(stmt.lclock());
    tchecker::range_t<tchecker::clock_id_t> rclocks = tchecker::extract_lvalue_variable_ids(stmt.rclock());
    tchecker::integer_t value = tchecker::const_evaluate(stmt.value(), 0); // 0 is worst estimation w.r.t. constraints

    for (tchecker::clock_id_t lclock = lclocks.begin(); lclock != lclocks.end(); ++lclock)
      for (tchecker::clock_id_t rclock = rclocks.begin(); rclock != rclocks.end(); ++rclock)
        _solver->add_assignment(_src, _tgt, lclock, rclock, value);
  }

  // Other visitors on statements
  virtual void visit(tchecker::typed_nop_statement_t const &) {}
  virtual void visit(tchecker::typed_assign_statement_t const &) {}
  virtual void visit(tchecker::typed_local_var_statement_t const & stmt) {}
  virtual void visit(tchecker::typed_local_array_statement_t const & stmt) {}

protected:
  tchecker::loc_id_t _src;                                     /*!< Source location ID */
  tchecker::loc_id_t _tgt;                                     /*!< Target location ID */
  std::shared_ptr<tchecker::clockbounds::df_solver_t> _solver; /*!< Solver */
};

/*!
  \class assigned_clocks_extractor_t
  \brief Computes the set of clock IDs that are *surely* assigned in a statement. While it is possible to determine
  the ID of a clocks that is assigned when the lvalue is a single clock (i.e. x := e), this is not possible when the
  lvalue base variable is an array (i.e. y[e] := f). This class computes the set of clocks that are assigned and that
  can be identified. In the example above, x is such a clock, while y is not, unless expression e is a constant
  expression that can be evaluated statically, then we can identify which cell of array y is assigned
*/
template <class INSERT_ITERATOR> class assigned_clocks_extractor_t : public tchecker::typed_statement_visitor_t {
public:
  /*!
  \brief Constructor
  */
  assigned_clocks_extractor_t(INSERT_ITERATOR & inserter) : _inserter(inserter) {}

  /*!
  \brief Copy constructor
  */
  assigned_clocks_extractor_t(tchecker::clockbounds::assigned_clocks_extractor_t<INSERT_ITERATOR> const &) = default;

  /*!
  \brief Move constructor
  */
  assigned_clocks_extractor_t(tchecker::clockbounds::assigned_clocks_extractor_t<INSERT_ITERATOR> &&) = default;

  /*!
  \brief Destructor
  */
  virtual ~assigned_clocks_extractor_t() = default;

  /*!
  \brief Assignment operator
  */
  tchecker::clockbounds::assigned_clocks_extractor_t<INSERT_ITERATOR> &
  operator=(tchecker::clockbounds::assigned_clocks_extractor_t<INSERT_ITERATOR> const &) = default;

  /*!
  \brief Move assignment operator
  */
  tchecker::clockbounds::assigned_clocks_extractor_t<INSERT_ITERATOR> &
  operator=(tchecker::clockbounds::assigned_clocks_extractor_t<INSERT_ITERATOR> &&) = default;

  /*!
  \brief Visitor
  \post first and second statements have been visited
  */
  virtual void visit(tchecker::typed_sequence_statement_t const & stmt)
  {
    stmt.first().visit(*this);
    stmt.second().visit(*this);
  }

  /*!
  \brief Visitor
  \post then_stmt and else_stmt statements have been visited
  */
  virtual void visit(tchecker::typed_if_statement_t const & stmt)
  {
    stmt.then_stmt().visit(*this);
    stmt.else_stmt().visit(*this);
  }

  /*!
  \brief Visitor
  \post stmt statement has been visited
  */
  virtual void visit(tchecker::typed_while_statement_t const & stmt) { stmt.statement().visit(*this); }

  /*!
  \brief Visitor
  \post the base clock of the lvalue of stmt has been inserted if its ID can be determined
  */
  virtual void visit(tchecker::typed_int_to_clock_assign_statement_t const & stmt)
  {
    tchecker::range_t<tchecker::variable_id_t> range = tchecker::extract_lvalue_variable_ids(stmt.clock());
    if (range.begin() + 1 == range.end())
      _inserter = range.begin();
  }

  /*!
  \brief Visitor
  \post the base clock of the lvalue of stmt has been inserted if its ID can be determined
  */
  virtual void visit(tchecker::typed_clock_to_clock_assign_statement_t const & stmt)
  {
    tchecker::range_t<tchecker::variable_id_t> range = tchecker::extract_lvalue_variable_ids(stmt.lclock());
    if (range.begin() + 1 == range.end())
      _inserter = range.begin();
  }

  /*!
  \brief Visitor
  \post the base clock of the lvalue of stmt has been inserted if its ID can be determined
  */
  virtual void visit(tchecker::typed_sum_to_clock_assign_statement_t const & stmt)
  {
    tchecker::range_t<tchecker::variable_id_t> range = tchecker::extract_lvalue_variable_ids(stmt.lclock());
    if (range.begin() + 1 == range.end())
      _inserter = range.begin();
  }

  // Other visitors
  virtual void visit(tchecker::typed_nop_statement_t const &) {}
  virtual void visit(tchecker::typed_assign_statement_t const &) {}
  virtual void visit(tchecker::typed_local_var_statement_t const & stmt) {}
  virtual void visit(tchecker::typed_local_array_statement_t const & stmt) {}

protected:
  INSERT_ITERATOR & _inserter; /*!< Inserter for assigned clock IDs */
};

/* add location/edge constraints to solver */

void add_location_constraints(tchecker::typed_expression_t const & inv, tchecker::loc_id_t loc,
                              std::shared_ptr<tchecker::clockbounds::df_solver_t> const & solver)
{
  tchecker::clockbounds::df_solver_updater_t updater(loc, loc, solver);
  inv.visit(updater);
}

void add_edge_constraints(tchecker::typed_expression_t const & guard, tchecker::typed_statement_t const & stmt,
                          tchecker::loc_id_t src, tchecker::loc_id_t tgt,
                          std::shared_ptr<tchecker::clockbounds::df_solver_t> const & solver)
{
  // guard and statement
  tchecker::clockbounds::df_solver_updater_t updater(src, tgt, solver);
  guard.visit(updater);
  stmt.visit(updater);

  // unassigned clocks
  std::unordered_set<tchecker::clock_id_t> assigned_clocks;
  auto assigned_clocks_inserter = std::inserter(assigned_clocks, assigned_clocks.begin());
  tchecker::clockbounds::assigned_clocks_extractor_t extractor(assigned_clocks_inserter);
  stmt.visit(extractor);

  tchecker::clock_id_t clock_number = solver->clock_number();
  for (tchecker::clock_id_t clock = 0; clock < clock_number; ++clock)
    if (assigned_clocks.find(clock) == assigned_clocks.end()) // clock is not assigned
      solver->add_no_assignement(src, tgt, clock);
}

/* solver */

std::shared_ptr<tchecker::clockbounds::df_solver_t> solve(tchecker::ta::system_t const & system)
{
  std::shared_ptr<tchecker::clockbounds::df_solver_t> solver(new tchecker::clockbounds::df_solver_t(system));

  for (tchecker::system::loc_const_shared_ptr_t const & loc : system.locations())
    tchecker::clockbounds::add_location_constraints(system.invariant(loc->id()), loc->id(), solver);

  for (tchecker::system::edge_const_shared_ptr_t const & edge : system.edges())
    tchecker::clockbounds::add_edge_constraints(system.guard(edge->id()), system.statement(edge->id()), edge->src(),
                                                edge->tgt(), solver);
  return solver;
}

/* fill clock bounds map */

void fill_global_lu_map(tchecker::clockbounds::df_solver_t const & solver, tchecker::clockbounds::global_lu_map_t & map)
{
  if (solver.clock_number() != map.clock_number())
    throw std::invalid_argument("solver and global LU map have incompatible clock numbers");

  if (!solver.has_solution())
    throw std::invalid_argument("clock bounds solver has no solution");

  tchecker::loc_id_t loc_nb = solver.loc_number();
  tchecker::clock_id_t clock_nb = solver.clock_number();

  for (tchecker::loc_id_t loc = 0; loc < loc_nb; ++loc)
    for (tchecker::clock_id_t clock = 0; clock < clock_nb; ++clock) {
      map.L()[clock] = std::max(solver.L(loc, clock), map.L()[clock]);
      map.U()[clock] = std::max(solver.U(loc, clock), map.U()[clock]);
    }
}

void fill_local_lu_map(tchecker::clockbounds::df_solver_t const & solver, tchecker::clockbounds::local_lu_map_t & map)
{
  if (solver.clock_number() != map.clock_number())
    throw std::invalid_argument("solver and local LU map have incompatible clock numbers");

  if (solver.loc_number() != map.loc_number())
    throw std::invalid_argument("solver and local LU map have incompatible location numbers");

  if (!solver.has_solution())
    throw std::invalid_argument("clock bounds solver has no solution");

  tchecker::loc_id_t loc_nb = solver.loc_number();
  tchecker::clock_id_t clock_nb = solver.clock_number();

  for (tchecker::loc_id_t loc = 0; loc < loc_nb; ++loc)
    for (tchecker::clock_id_t clock = 0; clock < clock_nb; ++clock) {
      map.L(loc)[clock] = solver.L(loc, clock);
      map.U(loc)[clock] = solver.U(loc, clock);
    }
}

void fill_global_m_map(tchecker::clockbounds::df_solver_t const & solver, tchecker::clockbounds::global_m_map_t & map)
{
  if (solver.clock_number() != map.clock_number())
    throw std::invalid_argument("solver and global M map have incomparible clock numbers");

  if (!solver.has_solution())
    throw std::invalid_argument("clock bounds solver has no solution");

  tchecker::loc_id_t loc_nb = solver.loc_number();
  tchecker::clock_id_t clock_nb = solver.clock_number();

  for (tchecker::loc_id_t loc = 0; loc < loc_nb; ++loc)
    for (tchecker::clock_id_t clock = 0; clock < clock_nb; ++clock)
      map.M()[clock] = std::max(map.M()[clock], std::max(solver.L(loc, clock), solver.U(loc, clock)));
}

void fill_local_m_map(tchecker::clockbounds::df_solver_t const & solver, tchecker::clockbounds::local_m_map_t & map)
{
  if (solver.clock_number() != map.clock_number())
    throw std::invalid_argument("solver and local M map have incompatible clock numbers");

  if (solver.loc_number() != map.loc_number())
    throw std::invalid_argument("solver and local M map have incompatible location numbers");

  if (!solver.has_solution())
    throw std::invalid_argument("clock bounds solver has no solution");

  tchecker::loc_id_t loc_nb = solver.loc_number();
  tchecker::clock_id_t clock_nb = solver.clock_number();

  for (tchecker::loc_id_t loc = 0; loc < loc_nb; ++loc)
    for (tchecker::clock_id_t clock = 0; clock < clock_nb; ++clock)
      map.M(loc)[clock] = std::max(solver.L(loc, clock), solver.U(loc, clock));
}

bool compute_clockbounds(tchecker::ta::system_t const & system, tchecker::clockbounds::clockbounds_t & clockbounds)
{
  // Solve
  std::shared_ptr<tchecker::clockbounds::df_solver_t> solver = tchecker::clockbounds::solve(system);
  if (!solver->has_solution())
    return false;

  // Fill the maps
  tchecker::clockbounds::fill_global_lu_map(*solver, *clockbounds.global_lu_map());
  tchecker::clockbounds::fill_local_lu_map(*solver, *clockbounds.local_lu_map());
  tchecker::clockbounds::fill_global_m_map(*solver, *clockbounds.global_m_map());
  tchecker::clockbounds::fill_local_m_map(*solver, *clockbounds.local_m_map());
  return true;
}

tchecker::clockbounds::clockbounds_t * compute_clockbounds(tchecker::ta::system_t const & system)
{
  tchecker::clockbounds::clockbounds_t * clockbounds =
      new tchecker::clockbounds::clockbounds_t{system.locations_count(), system.clocks_count(tchecker::VK_FLATTENED)};

  if (tchecker::clockbounds::compute_clockbounds(system, *clockbounds))
    return clockbounds;

  delete clockbounds;
  return nullptr;
}

} // end of namespace clockbounds

namespace amap {

  class amap_updater_t : public tchecker::typed_expression_visitor_t,
                         public tchecker::typed_statement_visitor_t 
  {
    public:
      /*!
      \brief Constructor
      \param G   : a set of diagonal constraints
      \param Gdf : a set of non-diagonal constraints
      */
      amap_updater_t(std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *> & G, std::vector<tchecker::typed_simple_clkconstr_expression_t const *> & Gdf)
      : _G(G), _Gdf(Gdf)
      {
      }

      /*!
      \brief Copy constructor
      \param updater : an updater
      \post this is a copy of updater
      */
      amap_updater_t(tchecker::amap::amap_updater_t const & updater)
          : _G(updater._G), _Gdf(updater._Gdf)
      {
      }

      /*!
      \brief Move constructor
      \param updater : an updater
      \post updater has been moved to this
      */
      amap_updater_t(tchecker::amap::amap_updater_t && updater) = delete;
      // amap_updater_t(tchecker::amap::amap_updater_t && updater)
      //     : _G(std::move(updater._G)), _Gdf(std::move(updater._Gdf))
      // {
      // }

      /*!
      \brief Destructor
      */
      ~amap_updater_t() = default;

      /*!
      \brief Assignment operator
      \param updater : an updater
      \post this is a copy of updater
      \return this
      */
      tchecker::amap::amap_updater_t & operator=(tchecker::amap::amap_updater_t const & updater)
      {
        if (this != &updater) {
          _G = updater._G;
          _Gdf = updater._Gdf;
        }
        return *this;
      }

      /*!
      \brief Move assignment operator
      \param updater : an updater
      \post updater has been moved to this
      \return this
      */
      tchecker::amap::amap_updater_t & operator=(tchecker::amap::amap_updater_t && updater)
      {
        if (this != &updater) {
          _G = std::move(updater._G);
          _Gdf = std::move(updater._Gdf);
        }
        return *this;
      }

      /*!
      \brief Visitor
      \post left and right operand have been visited if expr is a logical-and expression
      */
      virtual void visit(tchecker::typed_binary_expression_t const & expr)
      {
        if (expr.binary_operator() == tchecker::EXPR_OP_LAND) {
          expr.left_operand().visit(*this);
          expr.right_operand().visit(*this);
        }
      }

      /*!
      \brief Visitor
      \post sub-expression has been visited
      */
      virtual void visit(tchecker::typed_par_expression_t const & expr) { expr.expr().visit(*this); }

      /*!
      \brief Visitor
      \post expr is added to Gdf, if not present already
      */
      virtual void visit(tchecker::typed_simple_clkconstr_expression_t const & expr)
      {
        tchecker::integer_t expr_bound = tchecker::const_evaluate(expr.bound());
        // if expr is x == c, add x <= c, x >= c
        if (expr.binary_operator() == EXPR_OP_EQ)
        {
          tchecker::typed_expression_t * left = dynamic_cast<tchecker::typed_expression_t *>(expr.left_operand().clone());

          tchecker::typed_simple_clkconstr_expression_t * le_expr, * ge_expr;

          le_expr = new tchecker::typed_simple_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_SIMPLE, EXPR_OP_LE, left, new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, expr_bound));
          ge_expr = new tchecker::typed_simple_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_SIMPLE, EXPR_OP_GE, left, new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, expr_bound));

          add_constraint(*le_expr, _G, _Gdf);
          add_constraint(*ge_expr, _G, _Gdf);
          return;
        }

        // extracting details of expr
        tchecker::clock_id_t expr_x;
        expr_x = tchecker::extract_lvalue_variable_ids(expr.clock()).begin();
        tchecker::binary_operator_t expr_op = expr.binary_operator();

        // do not add expr to _G if _G already contains expr'
        // where, expr' >= expr
        for (tchecker::typed_simple_clkconstr_expression_t const * nondiag : _Gdf)
        {
          // first, we check if nondiag and expr contains the same clock
          if (tchecker::extract_lvalue_variable_ids(nondiag->clock()).begin() == expr_x)
          {
            // if the binary operator present in nondiag and expr
            // are of the same type, we want to compare the bounds
            if (((nondiag->binary_operator() == EXPR_OP_GE || 
                  nondiag->binary_operator() == EXPR_OP_GT) &&
                 (expr_op == EXPR_OP_GE || expr_op == EXPR_OP_GT)) ||
                ((nondiag->binary_operator() == EXPR_OP_LE || 
                  nondiag->binary_operator() == EXPR_OP_LT) &&
                 (expr_op == EXPR_OP_LE || expr_op == EXPR_OP_LT))
               )
              {
                // if the bound in nondiag is >= the bound in expr
                // we do not need to add expr to _Gdf
                if (tchecker::const_evaluate(nondiag->bound()) >= expr_bound)
                  return;
              }
          }
        }

        _Gdf.push_back(&expr);
      }

      /*!
      \brief Visitor
      \post expr is added to G, if not present already
      */
      virtual void visit(tchecker::typed_diagonal_clkconstr_expression_t const & expr)
      {
        tchecker::integer_t expr_bound = tchecker::const_evaluate(expr.bound());
        
        // if expr is x-y == c, add x-y <= c, x-y >= c
        if (expr.binary_operator() == EXPR_OP_EQ)
        {
          tchecker::typed_expression_t * left = dynamic_cast<tchecker::typed_expression_t *>(expr.left_operand().clone());

          tchecker::typed_diagonal_clkconstr_expression_t * le_expr, * ge_expr;

          le_expr = new tchecker::typed_diagonal_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_DIAGONAL, EXPR_OP_LE, left, new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, expr_bound));
          ge_expr = new tchecker::typed_diagonal_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_DIAGONAL, EXPR_OP_GE, left, new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, expr_bound));

          add_constraint(*le_expr, _G, _Gdf);
          add_constraint(*ge_expr, _G, _Gdf);
          return;
        }

        // extracting details of expr
        tchecker::clock_id_t expr_x, expr_y;
        expr_x = tchecker::extract_lvalue_variable_ids(expr.first_clock()).begin();
        expr_y = tchecker::extract_lvalue_variable_ids(expr.second_clock()).begin();
        tchecker::binary_operator_t expr_op = expr.binary_operator();

        // if expr is already present in _G, do not add
        for (tchecker::typed_diagonal_clkconstr_expression_t const * diag : _G)
        {
          if (tchecker::extract_lvalue_variable_ids(diag->first_clock()).begin() == expr_x &&
              tchecker::extract_lvalue_variable_ids(diag->second_clock()).begin() == expr_y &&
              diag->binary_operator() == expr_op &&
              tchecker::const_evaluate(diag->bound()) == expr_bound)
            return;
        }
        _G.push_back(&expr);
      }

      // Other visitors on expressions
      virtual void visit(tchecker::typed_int_expression_t const &) {}
      virtual void visit(tchecker::typed_var_expression_t const &) {}
      virtual void visit(tchecker::typed_bounded_var_expression_t const &) {}
      virtual void visit(tchecker::typed_array_expression_t const &) {}
      virtual void visit(tchecker::typed_unary_expression_t const &) {}
      virtual void visit(tchecker::typed_ite_expression_t const &) {}

      /*!
      \brief Visitor
      \post first and second statements have been visited
      */
      virtual void visit(tchecker::typed_sequence_statement_t const & stmt)
      {
        stmt.first().visit(*this);
        stmt.second().visit(*this);
      }

      /*!
      \brief Visitor
      \post condition expression, then_stmt, else_stmt are visited
      */
      virtual void visit(tchecker::typed_if_statement_t const & stmt)
      {
        stmt.condition().visit(*this);
        stmt.then_stmt().visit(*this);
        stmt.else_stmt().visit(*this);
      }

      /*!
      \brief Visitor
      \post condition expression and stmt statement are visited
      */
      virtual void visit(tchecker::typed_while_statement_t const & stmt)
      {
        stmt.condition().visit(*this);
        stmt.statement().visit(*this);
      }

      /*!
      \brief Visitor
      \post For assignment x:=y+c, a constraint for every clock x (x could be an array) and every clock y (y could be
      an array) using value c has been added to _solver using method add_assignment
      */
      virtual void visit(tchecker::typed_sum_to_clock_assign_statement_t const & stmt)
      {
        tchecker::clock_id_t clk_x = tchecker::extract_lvalue_variable_ids(stmt.lclock()).begin();
        tchecker::clock_id_t clk_y = tchecker::extract_lvalue_variable_ids(stmt.rclock()).begin();
        if (clk_x != clk_y) return;

        tchecker::integer_t value = tchecker::const_evaluate(stmt.value());
        if (value >= 0) return;

        // add the constraint x>=c to _Gdf
        tchecker::typed_var_expression_t const * stmt_x = dynamic_cast<tchecker::typed_var_expression_t const *>(& stmt.lclock());
        assert(stmt_x != nullptr);

        tchecker::typed_simple_clkconstr_expression_t const * x_ge_c = new tchecker::typed_simple_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_SIMPLE, EXPR_OP_GE, new tchecker::typed_var_expression_t(EXPR_TYPE_CLKVAR, stmt_x->name(), stmt_x->id(), stmt_x->size()), new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, -value));

        tchecker::amap::add_constraint(*x_ge_c, _G, _Gdf);
      }

      // Other visitors on statements
      virtual void visit(tchecker::typed_int_to_clock_assign_statement_t const &) {}
      virtual void visit(tchecker::typed_clock_to_clock_assign_statement_t const &) {}
      virtual void visit(tchecker::typed_nop_statement_t const &) {}
      virtual void visit(tchecker::typed_assign_statement_t const &) {}
      virtual void visit(tchecker::typed_local_var_statement_t const & stmt) {}
      virtual void visit(tchecker::typed_local_array_statement_t const & stmt) {}

    protected:
      std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *> & _G;
      std::vector<tchecker::typed_simple_clkconstr_expression_t const *> & _Gdf;
  };

  void add_constraint(tchecker::typed_expression_t const & g, std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *> & G, 
  std::vector<tchecker::typed_simple_clkconstr_expression_t const *> & Gdf)
  {
    tchecker::amap::amap_updater_t updater(G, Gdf);
    g.visit(updater);
  }

  class update_extractor_t : public tchecker::typed_statement_visitor_t
  {
    public:
      update_extractor_t(tchecker::typed_lvalue_expression_t const & clk,
                         tchecker::typed_expression_t *& z1,
                         tchecker::typed_expression_t *& d1)
                         : _clk(&clk), _z1(z1), _d1(d1)
      {}

      /*!
      \brief Copy constructor
      \param extractor : an extractor
      \post this is a copy of extractor
      */
      update_extractor_t(tchecker::amap::update_extractor_t const & extractor)
          : _clk(extractor._clk), _z1(extractor._z1), _d1(extractor._d1)
      {}

      /*!
      \brief Move constructor
      \param extractor : an extractor
      \post extractor has been moved to this
      */
      update_extractor_t(tchecker::amap::update_extractor_t &&) = delete;
      // update_extractor_t(tchecker::amap::update_extractor_t && extractor)
      //     : _clk(std::move(extractor._clk)), _z1(std::move(extractor._z1)), _d1(std::move(extractor._d1))
      // {}

      /*!
      \brief Destructor
      */
      ~update_extractor_t() = default;

      /*!
      \brief Assignment operator
      \param extractor : an extractor
      \post this is a copy of extractor
      \return this
      */
      tchecker::amap::update_extractor_t & operator=(tchecker::amap::update_extractor_t const & extractor)
      {
        if (this != &extractor) {
          _clk = extractor._clk;
          _z1 = extractor._z1;
          _d1 = extractor._d1;
        }
        return *this;
      }

      /*!
      \brief Move assignment operator
      \param extractor : an extractor
      \post extractor has been moved to this
      \return this
      */
      tchecker::amap::update_extractor_t & operator=(tchecker::amap::update_extractor_t && extractor)
      {
        if (this != &extractor) {
          _clk = std::move(extractor._clk);
          _z1 = std::move(extractor._z1);
          _d1 = std::move(extractor._d1);
        }
        return *this;
      }

      /*!
      \brief Visitor
      \post first and second statements have been visited
      */
      virtual void visit(tchecker::typed_sequence_statement_t const & stmt)
      {
        stmt.first().visit(*this);
        stmt.second().visit(*this);
      }

      /*!
      \brief Visitor
      \post For assignment x:=y+c, a constraint for every clock x (x could be an array) and every clock y (y could be
      an array) using value c has been added to _solver using method add_assignment
      */
      virtual void visit(tchecker::typed_sum_to_clock_assign_statement_t const & stmt)
      {
        if (dynamic_cast<tchecker::typed_var_expression_t const *>(_clk)->id() != dynamic_cast<tchecker::typed_var_expression_t const *>(& stmt.lclock())->id()) return;

        tchecker::typed_var_expression_t const * stmt_clk = dynamic_cast<tchecker::typed_var_expression_t const *>(& stmt.rclock());
        
        _z1 = new tchecker::typed_var_expression_t(EXPR_TYPE_CLKVAR, stmt_clk->name(), stmt_clk->id(), stmt_clk->size());
        _d1 = new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, tchecker::const_evaluate(stmt.value()));

        // delete stmt_clk;
      }

      virtual void visit(tchecker::typed_clock_to_clock_assign_statement_t const & stmt) 
      {
        if (dynamic_cast<tchecker::typed_var_expression_t const *>(_clk)->id() != dynamic_cast<tchecker::typed_var_expression_t const *>(& stmt.lclock())->id()) return;

        tchecker::typed_var_expression_t const * stmt_clk = dynamic_cast<tchecker::typed_var_expression_t const *>(& stmt.rclock());
        
        _z1 = new tchecker::typed_var_expression_t(EXPR_TYPE_CLKVAR, stmt_clk->name(), stmt_clk->id(), stmt_clk->size());
        _d1 = nullptr;
        
        // delete stmt_clk;
      }

      virtual void visit(tchecker::typed_int_to_clock_assign_statement_t const & stmt) 
      {
        if (dynamic_cast<tchecker::typed_var_expression_t const *>(_clk)->id() != dynamic_cast<tchecker::typed_var_expression_t const *>(& stmt.clock())->id()) return;

        _z1 = nullptr;
        _d1 = new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, tchecker::const_evaluate(stmt.value()));
      }

      // Other visitors on statements
      virtual void visit(tchecker::typed_if_statement_t const & stmt) {}
      virtual void visit(tchecker::typed_while_statement_t const & stmt) {}
      virtual void visit(tchecker::typed_nop_statement_t const &) {}
      virtual void visit(tchecker::typed_assign_statement_t const &) {}
      virtual void visit(tchecker::typed_local_var_statement_t const & stmt) {}
      virtual void visit(tchecker::typed_local_array_statement_t const & stmt) {}

    protected:
      tchecker::typed_lvalue_expression_t const * _clk;
      tchecker::typed_expression_t *& _z1;
      tchecker::typed_expression_t *& _d1;
  };

  enum available_optimizations_t {
    NO_OPTIM,
    ROW1,
    ROW2,
    ROW3
  };

  bool lleq(tchecker::binary_operator_t op)
  {
    if (op == EXPR_OP_LT || op == EXPR_OP_LE)
      return true;
    return false;
  }

  bool ggeq(tchecker::binary_operator_t op)
  {
    if (op == EXPR_OP_GT || op == EXPR_OP_GE)
      return true;
    return false;
  }

  class pre_optimizer_t : public tchecker::typed_expression_visitor_t
  {
    public:
      /*!
      \brief Constructor
      tchecker::variable_id_t const * _clk1, * _clk2;
      tchecker::binary_operator_t _op;
      tchecker::integer_t * _bound, * _newbound;
      enum tchecker::amap::available_optimizations_t _row;
      bool _satisfied;
      */
      pre_optimizer_t(tchecker::variable_id_t const & clk1,
                      tchecker::variable_id_t const & clk2,
                      tchecker::integer_t bound,
                      tchecker::integer_t & newbound,
                      enum tchecker::amap::available_optimizations_t row,
                      bool & satisfied)
      : _clk1(clk1), _clk2(clk2), _bound(bound), _newbound(newbound), _row(row), _satisfied(satisfied)
      {
      }

      /*!
      \brief Copy constructor
      \param updater : an updater
      \post this is a copy of updater
      */
      pre_optimizer_t(tchecker::amap::pre_optimizer_t const & optimizer)
          : _clk1(optimizer._clk1), _clk2(optimizer._clk2), _bound(optimizer._bound), _newbound(optimizer._newbound), _row(optimizer._row), _satisfied(optimizer._satisfied)
      {
      }

      /*!
      \brief Move constructor
      \param updater : an updater
      \post updater has been moved to this
      */
      pre_optimizer_t(tchecker::amap::pre_optimizer_t && ) = delete;
          
      // pre_optimizer_t(tchecker::amap::pre_optimizer_t && optimizer)
      //     : _clk1(std::move(optimizer._clk1)), _clk2(std::move(optimizer._clk2)), _bound(std::move(optimizer._bound)), _newbound(std::move(optimizer._newbound)), _row(std::move(optimizer._row)), _satisfied(std::move(optimizer._satisfied))
      // {
      // }

      /*!
      \brief Destructor
      */
      ~pre_optimizer_t() = default;

      // /*!
      // \brief Assignment operator
      // \param updater : an updater
      // \post this is a copy of updater
      // \return this
      // */
      // tchecker::amap::pre_optimizer_t & operator=(tchecker::amap::pre_optimizer_t const & optimizer)
      // {
      //   // if (this != &optimizer) {
      //   //   _clk1     = optimizer._clk1; 
      //   //   _clk2     = optimizer._clk2;
      //   //   _op       = optimizer._op;
      //   //   _bound    = optimizer._bound;
      //   //   _newbound = optimizer._newbound; 
      //   //   _row      = optimizer._row;
      //   //   _satisfied = optimizer._satisfied;
      //   // }
      //   // return *this;
      // }

      // /*!
      // \brief Move assignment operator
      // \param updater : an updater
      // \post updater has been moved to this
      // \return this
      // */
      // tchecker::amap::pre_optimizer_t & operator=(tchecker::amap::pre_optimizer_t && optimizer)
      // {
      //   // if (this != &optimizer) {
      //   //   _clk1     = std::move(optimizer._clk1); 
      //   //   _clk2     = std::move(optimizer._clk2);
      //   //   _op       = std::move(optimizer._op);
      //   //   _bound    = std::move(optimizer._bound);
      //   //   _newbound = std::move(optimizer._newbound); 
      //   //   _row1     = std::move(optimizer._row1); 
      //   //   _row2     = std::move(optimizer._row2); 
      //   //   _row3     = std::move(optimizer._row3);
      //   // }
      //   // return *this;
      // }

      /*!
      \brief Visitor
      \post left and right operand have been visited if expr is a logical-and expression
      */
      virtual void visit(tchecker::typed_binary_expression_t const & expr)
      {
        if (expr.binary_operator() == tchecker::EXPR_OP_LAND) {
          expr.left_operand().visit(*this);
          expr.right_operand().visit(*this);
        }
      }

      /*!
      \brief Visitor
      \post sub-expression has been visited
      */
      virtual void visit(tchecker::typed_par_expression_t const & expr) { expr.expr().visit(*this); }

      /*!
      \brief Visitor
      \post expr is added to Gdf
      */
      virtual void visit(tchecker::typed_simple_clkconstr_expression_t const & expr)
      {
        if (_clk1 != tchecker::extract_lvalue_variable_ids(expr.clock()).begin()) return;

        if (_row == ROW1 && lleq(expr.binary_operator()))
          _satisfied = true;

        if (lleq(expr.binary_operator()) && 
            tchecker::const_evaluate(expr.bound()) < _bound)
        {
          if (_row == ROW2)
          {
            _newbound = tchecker::const_evaluate(expr.bound());
            _satisfied = true;
          }
          if (_row == ROW3) _satisfied = true;
        }
      }

      /*!
      \brief Visitor
      */
      virtual void visit(tchecker::typed_diagonal_clkconstr_expression_t const & expr)
      {
        if (_clk1 != tchecker::extract_lvalue_variable_ids(expr.first_clock()).begin()) return;
        if (_clk2 != tchecker::extract_lvalue_variable_ids(expr.second_clock()).begin()) return;

        tchecker::integer_t expr_const = tchecker::const_evaluate(expr.bound());

        if (_row == ROW3 && ( (lleq(expr.binary_operator()) && 
                                expr_const < _bound) || 
                              (ggeq(expr.binary_operator()) && 
                                _bound < expr_const) 
                            ))
          _satisfied = true;
      }

      // Other visitors on expressions
      virtual void visit(tchecker::typed_int_expression_t const &) {}
      virtual void visit(tchecker::typed_var_expression_t const &) {}
      virtual void visit(tchecker::typed_bounded_var_expression_t const &) {}
      virtual void visit(tchecker::typed_array_expression_t const &) {}
      virtual void visit(tchecker::typed_unary_expression_t const &) {}
      virtual void visit(tchecker::typed_ite_expression_t const &) {}

    protected:
      tchecker::variable_id_t const _clk1, _clk2;
      tchecker::integer_t _bound; 
      tchecker::integer_t & _newbound;
      enum tchecker::amap::available_optimizations_t _row;
      bool & _satisfied;
  };

  void guard_based_optimization(tchecker::typed_expression_t *& pre,
                                tchecker::typed_expression_t const & g)
  {
    assert( pre->type() == EXPR_TYPE_CLKCONSTR_SIMPLE ||
            pre->type() == EXPR_TYPE_CLKCONSTR_DIAGONAL );

    tchecker::integer_t pre_bound, newbound;
    bool satisfied = false;
    tchecker::amap::available_optimizations_t select_optimization = NO_OPTIM;

    tchecker::variable_id_t pre_clk1, pre_clk2;

    if (pre->type() == EXPR_TYPE_CLKCONSTR_SIMPLE) {
      tchecker::typed_simple_clkconstr_expression_t const * pre_nondiag = dynamic_cast<tchecker::typed_simple_clkconstr_expression_t const *>(pre);
      pre_clk1 = extract_lvalue_variable_ids(pre_nondiag->clock()).begin();
      pre_clk2 = pre_clk1;

      if (lleq(pre_nondiag->binary_operator()))
        select_optimization = ROW1;
    
      if (ggeq(pre_nondiag->binary_operator()))
        select_optimization = ROW2;

      pre_bound = tchecker::const_evaluate(pre_nondiag->bound());
    }

    if (pre->type() == EXPR_TYPE_CLKCONSTR_DIAGONAL) {
      tchecker::typed_diagonal_clkconstr_expression_t const * pre_diag = dynamic_cast<tchecker::typed_diagonal_clkconstr_expression_t const *>(pre);
      pre_clk1 = extract_lvalue_variable_ids(pre_diag->first_clock()).begin();
      pre_clk2 = extract_lvalue_variable_ids(pre_diag->second_clock()).begin();

      select_optimization = ROW3;

      pre_bound = tchecker::const_evaluate(pre_diag->bound());
    }

    tchecker::amap::pre_optimizer_t optimizer(pre_clk1, pre_clk2, pre_bound, newbound, select_optimization, satisfied);
    g.visit(optimizer);

    if ((select_optimization == ROW1 || select_optimization == ROW3) &&
        satisfied) 
      pre = nullptr;
    if (select_optimization == ROW2 && satisfied)
    {
      tchecker::typed_var_expression_t const * clk_in_pre = dynamic_cast<tchecker::typed_var_expression_t const *>(& dynamic_cast<tchecker::typed_simple_clkconstr_expression_t const *>(pre)->clock());
      
      // pre := clk_in_pre >= newbound
      pre = new tchecker::typed_simple_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_SIMPLE, EXPR_OP_GE, 
      new tchecker::typed_var_expression_t(EXPR_TYPE_CLKVAR, clk_in_pre->name(), clk_in_pre->id(), clk_in_pre->size()), 
      new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, newbound));

      // delete clk_in_pre;
    }
  }

  tchecker::binary_operator_t reverse_operator(tchecker::binary_operator_t op)
  {
    assert(predicate(op)); // op ::= < | <= | = | != | >= | >
    tchecker::binary_operator_t newop = op;
    if (op == EXPR_OP_LE) newop = EXPR_OP_GE;
    if (op == EXPR_OP_LT) newop = EXPR_OP_GT;
    if (op == EXPR_OP_GE) newop = EXPR_OP_LE;
    if (op == EXPR_OP_GT) newop = EXPR_OP_LT;
    return newop;
  }

  // construct the expression: z1 - z2 op' c - (d1 - d2) 
  // where either op' = op or op' = reverse_operator(op)
  void up_inverse(tchecker::typed_expression_t * z1,
                  tchecker::typed_expression_t const * d1,
                  tchecker::typed_expression_t * z2,
                  tchecker::typed_expression_t const * d2,
                  tchecker::binary_operator_t const & op,
                  tchecker::typed_expression_t const & c, 
                  tchecker::typed_expression_t *& upinv)
  {
    tchecker::integer_t cd1 = (d1 ? tchecker::const_evaluate(*d1) : 0);
    tchecker::integer_t cd2 = (d2 ? tchecker::const_evaluate(*d2) : 0);
    tchecker::integer_t final_const = tchecker::const_evaluate(c) - cd1 + cd2;

    bool to_be_reversed = false, upinv_is_diagonal = false;

    if (final_const < 0) to_be_reversed = true;
    
    tchecker::typed_expression_t * left = nullptr;
    if (z1 && z2 )
    {
      // if z1 and z2 are the same clock then upinv = T
      if (dynamic_cast<tchecker::typed_var_expression_t *>(z1)->id() == dynamic_cast<tchecker::typed_var_expression_t *>(z2)->id()) return;
      
      if (final_const >= 0)
        left = new tchecker::typed_binary_expression_t(EXPR_TYPE_CLKDIFF, EXPR_OP_MINUS, z1, z2);
      else
        left = new tchecker::typed_binary_expression_t(EXPR_TYPE_CLKDIFF, EXPR_OP_MINUS, z2, z1);
      upinv_is_diagonal = true;
    }
    if (z1 && !z2)
      left = z1;
    if (!z1 && z2) {
      left = z2; 
      to_be_reversed = true;
    }
    if (!z1 && !z2) return;

    final_const = to_be_reversed ? -final_const : final_const;
    if (final_const < 0) return;

    tchecker::typed_int_expression_t * right = new tchecker::typed_int_expression_t(EXPR_TYPE_INTTERM, final_const);

    tchecker::binary_operator_t newop = op;
    if (to_be_reversed) newop = reverse_operator(op);

    if (upinv_is_diagonal)
      upinv = new tchecker::typed_diagonal_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_DIAGONAL, newop, left, right);
    else
      upinv = new tchecker::typed_simple_clkconstr_expression_t(EXPR_TYPE_CLKCONSTR_SIMPLE, newop, left, right);
  }

  void extract_updates(tchecker::typed_statement_t const & up,
                       tchecker::typed_lvalue_expression_t const & clk,
                       tchecker::typed_expression_t *& z,
                       tchecker::typed_expression_t *& d)
  {
    tchecker::amap::update_extractor_t extractor(clk, z, d);
    up.visit(extractor);

    if (!z && !d)
    {
      tchecker::typed_var_expression_t const * clk_var = dynamic_cast<tchecker::typed_var_expression_t const *>(& clk);
      
      z = new tchecker::typed_var_expression_t(EXPR_TYPE_CLKVAR, clk_var->name(), clk_var->id(), clk_var->size());

      // delete clk_var;
    }
  }

  void compute_upinverse(tchecker::typed_simple_clkconstr_expression_t const * phi,
                   tchecker::typed_statement_t const & up,
                   tchecker::typed_expression_t * & pre)
  {
    tchecker::typed_expression_t * z1 = nullptr, * d1 = nullptr;

    extract_updates(up, phi->clock(), z1, d1);

    up_inverse(z1, d1, nullptr, nullptr, phi->binary_operator(), phi->bound(), pre);
  }

  void compute_upinverse(tchecker::typed_diagonal_clkconstr_expression_t const * phi,
                   tchecker::typed_statement_t const & up,
                   tchecker::typed_expression_t * & pre)
  {
    tchecker::typed_expression_t * z1 = nullptr, * d1 = nullptr;
    tchecker::typed_expression_t * z2 = nullptr, * d2 = nullptr;

    extract_updates(up, phi->first_clock(), z1, d1);
    extract_updates(up, phi->second_clock(), z2, d2);

    up_inverse(z1, d1, z2, d2, phi->binary_operator(), phi->bound(), pre);
  }

  template<typename EXPR>
  void compute_pre(EXPR const * phi,
                   tchecker::typed_expression_t const & g,
                   tchecker::typed_statement_t const & up,
                   tchecker::typed_expression_t * & pre)
  {
    assert( (phi->type() == EXPR_TYPE_CLKCONSTR_SIMPLE) || 
            (phi->type() == EXPR_TYPE_CLKCONSTR_DIAGONAL) );

    tchecker::amap::compute_upinverse(phi, up, pre);
    if (pre != nullptr)
      guard_based_optimization(pre, g);
  }

  class constant_extractor_t : public tchecker::typed_expression_visitor_t, 
                               public tchecker::typed_statement_visitor_t
  {
    public:
      /*!
      \brief Constructor
      tchecker::integer_t * _max
      */
      constant_extractor_t()
      : _constant(0)
      {
      }

      /*!
      \brief Copy constructor
      \param updater : an updater
      \post this is a copy of updater
      */
      constant_extractor_t(tchecker::amap::constant_extractor_t const & optimizer)
          : _constant(optimizer._constant)
      {
      }

      /*!
      \brief Move constructor
      \param updater : an updater
      \post updater has been moved to this
      */
      constant_extractor_t(tchecker::amap::constant_extractor_t && optimizer)
          : _constant(std::move(optimizer._constant))
      {
      }

      /*!
      \brief Destructor
      */
      ~constant_extractor_t() = default;

      /*!
      \brief Accessor
      \return constant
      */
      inline tchecker::integer_t constant() const { return _constant; }

      /*!
      \brief Visitor
      \post sub-expression has been visited
      */
      virtual void visit(tchecker::typed_par_expression_t const & expr) { expr.expr().visit(*this); }

      /*!
      \brief Visitor
      \post expr is added to Gdf
      */
      virtual void visit(tchecker::typed_simple_clkconstr_expression_t const & expr)
      {
        _constant = tchecker::const_evaluate(expr.bound());
      }

      /*!
      \brief Visitor
      */
      virtual void visit(tchecker::typed_diagonal_clkconstr_expression_t const & expr)
      {
        _constant = tchecker::const_evaluate(expr.bound());
      }

      /*!
      \brief Visitor
      */
      virtual void visit(tchecker::typed_binary_expression_t const & expr) 
      { 
        tchecker::amap::constant_extractor_t extractor1;
        tchecker::amap::constant_extractor_t extractor2;

        expr.left_operand().visit(extractor1);
        expr.right_operand().visit(extractor2);
        
        _constant = std::max(extractor1.constant(), extractor2.constant());
      }

      // Other visitors on expressions
      virtual void visit(tchecker::typed_int_expression_t const &) { }
      virtual void visit(tchecker::typed_var_expression_t const &) { }
      virtual void visit(tchecker::typed_bounded_var_expression_t const &) { }
      virtual void visit(tchecker::typed_array_expression_t const &) { }
      virtual void visit(tchecker::typed_unary_expression_t const &) { }
      virtual void visit(tchecker::typed_ite_expression_t const &) { }

      /*!
      \brief Visitor
      \post first and second statements have been visited
      */
      virtual void visit(tchecker::typed_sequence_statement_t const & stmt)
      {
        tchecker::amap::constant_extractor_t extractor1, extractor2;
        stmt.first().visit(extractor1);
        stmt.second().visit(extractor2);
        _constant = std::max(extractor1.constant(), extractor2.constant());
      }

      /*!
      \brief Visitor
      \post For assignment x:=y+c, a constraint for every clock x (x could be an array) and every clock y (y could be
      an array) using value c has been added to _solver using method add_assignment
      */
      virtual void visit(tchecker::typed_sum_to_clock_assign_statement_t const & stmt)
      {
        _constant = tchecker::const_evaluate(stmt.value());
      }

      virtual void visit(tchecker::typed_int_to_clock_assign_statement_t const & stmt) 
      {
        _constant = tchecker::const_evaluate(stmt.value());
      }

      // Other visitors on statements
      virtual void visit(tchecker::typed_if_statement_t const & stmt) {}
      virtual void visit(tchecker::typed_while_statement_t const & stmt) {}
      virtual void visit(tchecker::typed_clock_to_clock_assign_statement_t const &) {}
      virtual void visit(tchecker::typed_nop_statement_t const &) {}
      virtual void visit(tchecker::typed_assign_statement_t const &) {}
      virtual void visit(tchecker::typed_local_var_statement_t const &) {}
      virtual void visit(tchecker::typed_local_array_statement_t const &) {}

    protected:
      tchecker::integer_t _constant;
  };

  tchecker::integer_t extract_constant(tchecker::typed_expression_t const & expr)
  {
    tchecker::amap::constant_extractor_t extractor;
    expr.visit(extractor);
    return extractor.constant();
  }

  template <typename EXPR>
  void propagate_constraint(EXPR const * phi, 
                            tchecker::typed_expression_t const & g,
                            tchecker::typed_statement_t const & up, 
                            std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *> & G,
                            std::vector<tchecker::typed_simple_clkconstr_expression_t const *> & Gdf,
                            tchecker::integer_t const & cutoff_bound,
                            bool & stabilized)
  {
    assert( (phi->type() == EXPR_TYPE_CLKCONSTR_SIMPLE) || 
            (phi->type() == EXPR_TYPE_CLKCONSTR_DIAGONAL) );
    
    tchecker::typed_expression_t * pre = nullptr;
    compute_pre<EXPR>(phi, g, up, pre);
    
    if (pre == nullptr)
      return;

    // if the constant in pre is more than cutoff_bound
    // the fixpoint iteration will not terminate
    if (extract_constant(*pre) > cutoff_bound)
      throw std::runtime_error("this algorithm cannot check reachability in this input automaton: non-terminating fixpoint computation");
    
    tchecker::amap::add_constraint(*pre, G, Gdf);
  }

  tchecker::integer_t find_cutoff_bound(tchecker::ta::system_t const & system)
  {
    tchecker::integer_t invariant_maxconst = 0, guard_maxconst = 0, update_maxconst = 0;

    tchecker::amap::constant_extractor_t invariant_extractor;
    tchecker::amap::constant_extractor_t guard_extractor;
    tchecker::amap::constant_extractor_t update_extractor;

    for (tchecker::system::loc_const_shared_ptr_t const & loc : system.locations())
    {
      system.invariant(loc->id()).visit(invariant_extractor);
      invariant_maxconst = std::max(invariant_maxconst, invariant_extractor.constant());
    }

    for (tchecker::system::edge_const_shared_ptr_t const & edge : system.edges())
    {
      system.guard(edge->id()).visit(guard_extractor);
      guard_maxconst = std::max(guard_maxconst, guard_extractor.constant());

      system.statement(edge->id()).visit(update_extractor);
      update_maxconst = std::max(update_maxconst, update_extractor.constant());
    }

    guard_maxconst = std::max(guard_maxconst, invariant_maxconst);

    tchecker::integer_t cutoff_bound = std::max(guard_maxconst, update_maxconst) + (2 * update_maxconst * system.locations_count() * system.clocks_count(tchecker::VK_FLATTENED) * system.clocks_count(tchecker::VK_FLATTENED));

    return cutoff_bound;
  }

  bool find_fixpoint(tchecker::ta::system_t const & system,
                     tchecker::amap::a_map_t & amap)
  {
    bool stabilized = false;
    tchecker::integer_t cutoff_bound = find_cutoff_bound(system);

    while (!stabilized)
    {
      stabilized = true;
      // for every edge of the automaton
      for (tchecker::system::edge_const_shared_ptr_t const & edge : system.edges())
      {
        size_t G_size_before = amap.G(edge->src()).size();
        size_t Gdf_size_before = amap.Gdf(edge->src()).size();

        tchecker::typed_expression_t const & guard = system.guard(edge->id());
        tchecker::typed_statement_t const & up = system.statement(edge->id());

        std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *> *G = nullptr;
        std::vector<tchecker::typed_simple_clkconstr_expression_t const *> *Gdf = nullptr;

        if (edge->src() != edge->tgt())
        {
          G = &amap.G(edge->src());
          Gdf = &amap.Gdf(edge->src());
        }
        else
        {
          G = new std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *>();
          Gdf = new std::vector<tchecker::typed_simple_clkconstr_expression_t const *>();
        }

        bool wrong_stabilized = true;

        // propagate every diagonal constraint from G[tgt] to G[src]
        for (tchecker::typed_diagonal_clkconstr_expression_t const * diag : amap.G(edge->tgt()))
          propagate_constraint<tchecker::typed_diagonal_clkconstr_expression_t>(diag, guard, up, *G, *Gdf, cutoff_bound, wrong_stabilized);

        // propagate every non-diagonal constraint from Gdf[tgt] to G[src]
        for (tchecker::typed_simple_clkconstr_expression_t const * nondiag : amap.Gdf(edge->tgt()))
        {
          propagate_constraint<tchecker::typed_simple_clkconstr_expression_t>(nondiag, guard, up, *G, *Gdf, cutoff_bound, wrong_stabilized);
        }

        if (edge->src() == edge->tgt())
        {
          for (auto & diag : *G)
            tchecker::amap::add_constraint(*diag, amap.G(edge->src()), amap.Gdf(edge->src()));
          
          G->clear();
          
          for (auto & nondiag : *Gdf)
            tchecker::amap::add_constraint(*nondiag, amap.G(edge->src()), amap.Gdf(edge->src()));
          
          Gdf->clear();
        }

        if (amap.G(edge->src()).size() != G_size_before ||
            amap.Gdf(edge->src()).size() != Gdf_size_before)
          stabilized = false;
      }
    }
    return true;
  }

  bool compute_amap(tchecker::ta::system_t const & system, tchecker::amap::a_map_t & amap)
  {
    // add atomic constraints in invariants to G[loc]
    for (tchecker::system::loc_const_shared_ptr_t const & loc : system.locations())
      tchecker::amap::add_constraint(system.invariant(loc->id()), 
                                     amap.G(loc->id()), 
                                     amap.Gdf(loc->id()));

    // add atomic constraints of guards to G[src], Gdf[src]
    // add constraint for updates x := -c + x to Gdf[src]
    for (tchecker::system::edge_const_shared_ptr_t const & edge : system.edges())
      tchecker::amap::add_constraint(system.guard(edge->id()),
                                     amap.G(edge->src()), 
                                     amap.Gdf(edge->src()));
    
    // compute fixpoint
    return find_fixpoint(system, amap);
  }

  tchecker::amap::a_map_t * compute_amap(tchecker::ta::system_t const & system)
  {
    tchecker::amap::a_map_t * amap =
        new tchecker::amap::a_map_t{system.locations_count()};

    if (tchecker::amap::compute_amap(system, *amap))
    {
      // std::cout << *amap << std::endl;
      return amap;
    }

    delete amap;
    return nullptr;
  }

} // end of namespace amap

} // end of namespace tchecker
