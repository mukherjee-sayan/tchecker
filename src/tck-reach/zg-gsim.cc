/*
 * This file is a part of the TChecker project.
 *
 * See files AUTHORS and LICENSE for copyright details.
 *
 */

#include <boost/dynamic_bitset.hpp>

#include "tchecker/algorithms/search_order.hh"
#include "tchecker/ta/state.hh"
#include "zg-gsim.hh"

namespace tchecker {

namespace tck_reach {

namespace zg_gsim {

/* node_t */

node_t::node_t(tchecker::zg::state_sptr_t const & s) : _state(s) {}

node_t::node_t(tchecker::zg::const_state_sptr_t const & s) : _state(s) {}

/* node_hash_t */

std::size_t node_hash_t::operator()(tchecker::tck_reach::zg_gsim::node_t const & n) const
{
  // NB: we hash on the discrete part of the state in n to check all nodes
  // with same discrete part for covering
  return tchecker::ta::hash_value(n.state());
}

/* node_le_t */

node_le_t::node_le_t(tchecker::amap::a_map_t const & amap) : _amap(amap), _G(new std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *>()), _Gdf(new std::vector<tchecker::typed_simple_clkconstr_expression_t const *>())
{
}

node_le_t::node_le_t(tchecker::ta::system_t const & system) : _amap(*tchecker::amap::compute_amap(system)), _G(new std::vector<tchecker::typed_diagonal_clkconstr_expression_t const *>()), _Gdf(new std::vector<tchecker::typed_simple_clkconstr_expression_t const *>())
{
}

node_le_t::node_le_t(tchecker::tck_reach::zg_gsim::node_le_t const & node_le) : _amap(node_le._amap), _G(node_le._G), _Gdf(node_le._Gdf)
{
}

node_le_t::node_le_t(tchecker::tck_reach::zg_gsim::node_le_t && node_le) : _amap(std::move(node_le._amap)), _G(std::move(node_le._G)), _Gdf(std::move(node_le._Gdf))
{
  node_le._G = nullptr;
  node_le._Gdf = nullptr;
}

node_le_t::~node_le_t()
{
  _G = nullptr;
  _Gdf = nullptr;
}

bool node_le_t::operator()(tchecker::tck_reach::zg_gsim::node_t const & n1,
                           tchecker::tck_reach::zg_gsim::node_t const & n2) const
{
  _amap.bounds(n2.state().vloc(), *_G, *_Gdf);
  return tchecker::zg::g_le(n1.state(), n2.state(), *_G, *_Gdf);
}

/* edge_t */

edge_t::edge_t(tchecker::zg::transition_t const & t) : _vedge(t.vedge_ptr()) {}

/* graph_t */

graph_t::graph_t(std::shared_ptr<tchecker::zg::zg_t> const & zg, std::size_t block_size, std::size_t table_size)
    : tchecker::graph::subsumption::graph_t<tchecker::tck_reach::zg_gsim::node_t, tchecker::tck_reach::zg_gsim::edge_t,
                                            tchecker::tck_reach::zg_gsim::node_hash_t,
                                            tchecker::tck_reach::zg_gsim::node_le_t>(
          block_size, table_size, tchecker::tck_reach::zg_gsim::node_hash_t(),
          tchecker::tck_reach::zg_gsim::node_le_t(zg->system())),
      _zg(zg)
{
}

graph_t::~graph_t()
{
  tchecker::graph::subsumption::graph_t<tchecker::tck_reach::zg_gsim::node_t, tchecker::tck_reach::zg_gsim::edge_t,
                                        tchecker::tck_reach::zg_gsim::node_hash_t,
                                        tchecker::tck_reach::zg_gsim::node_le_t>::clear();
}

void graph_t::attributes(tchecker::tck_reach::zg_gsim::node_t const & n, std::map<std::string, std::string> & m) const
{
  _zg->attributes(n.state_ptr(), m);
}

void graph_t::attributes(tchecker::tck_reach::zg_gsim::edge_t const & e, std::map<std::string, std::string> & m) const
{
  m["vedge"] = tchecker::to_string(e.vedge(), _zg->system().as_system_system());
}

/* dot_output */

/*!
 \class node_lexical_less_t
 \brief Less-than order on nodes based on lexical ordering
*/
class node_lexical_less_t {
public:
  /*!
   \brief Less-than order on nodes based on lexical ordering
   \param n1 : a node
   \param n2 : a node
   \return true if n1 is less-than n2 w.r.t. lexical ordering over the states in
   the nodes
  */
  bool operator()(tchecker::tck_reach::zg_gsim::graph_t::node_sptr_t const & n1,
                  tchecker::tck_reach::zg_gsim::graph_t::node_sptr_t const & n2) const
  {
    return tchecker::zg::lexical_cmp(n1->state(), n2->state()) < 0;
  }
};

/*!
 \class edge_lexical_less_t
 \brief Less-than ordering on edges based on lexical ordering
 */
class edge_lexical_less_t {
public:
  /*!
   \brief Less-than ordering on edges based on lexical ordering
   \param e1 : an edge
   \param e2 : an edge
   \return true if e1 is less-than  e2 w.r.t. the tuple of edges in e1 and e2
  */
  bool operator()(tchecker::tck_reach::zg_gsim::graph_t::edge_sptr_t const & e1,
                  tchecker::tck_reach::zg_gsim::graph_t::edge_sptr_t const & e2) const
  {
    return tchecker::lexical_cmp(e1->vedge(), e2->vedge()) < 0;
  }
};

std::ostream & dot_output(std::ostream & os, tchecker::tck_reach::zg_gsim::graph_t const & g, std::string const & name)
{
  return tchecker::graph::subsumption::dot_output<tchecker::tck_reach::zg_gsim::graph_t,
                                                  tchecker::tck_reach::zg_gsim::node_lexical_less_t,
                                                  tchecker::tck_reach::zg_gsim::edge_lexical_less_t>(os, g, name);
}

/* run */

std::tuple<tchecker::algorithms::covreach::stats_t, std::shared_ptr<tchecker::tck_reach::zg_gsim::graph_t>>
run(std::shared_ptr<tchecker::parsing::system_declaration_t> const & sysdecl, std::string const & labels,
    std::string const & search_order, std::size_t block_size, std::size_t table_size)
{
  std::shared_ptr<tchecker::ta::system_t const> system{new tchecker::ta::system_t{*sysdecl}};

  std::shared_ptr<tchecker::zg::zg_t> zg{
      tchecker::zg::factory(system, tchecker::zg::ELAPSED_SEMANTICS, tchecker::zg::NO_EXTRAPOLATION, block_size)};

  std::shared_ptr<tchecker::tck_reach::zg_gsim::graph_t> graph{
      new tchecker::tck_reach::zg_gsim::graph_t{zg, block_size, table_size}};

  boost::dynamic_bitset<> accepting_labels = system->as_syncprod_system().labels(labels);

  tchecker::tck_reach::zg_gsim::algorithm_t algorithm;

  enum tchecker::waiting::policy_t policy = tchecker::algorithms::fast_remove_waiting_policy(search_order);

  tchecker::algorithms::covreach::stats_t stats = algorithm.run(*zg, *graph, accepting_labels, policy);

  return std::make_tuple(stats, graph);
}

} // end of namespace zg_gsim

} // end of namespace tck_reach

} // end of namespace tchecker