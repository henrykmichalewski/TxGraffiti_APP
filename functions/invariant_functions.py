import grinpy as gp
import itertools

__all__ = ["compute"]


def compute(G, property):
    """
    Returns the value of a given graph property for a given graph G.

    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    property : string
        The name of the graph property to be calculated for the graph G.

    Returns
    -------
    int or float or bool
        The value of the graph property for the graph G.
    """
    if property == "k_slater_index":
        return k_slater_index(G)
    elif property == "vertex_cover_number":
        return vertex_cover_number(G)
    elif property == "k_residual_index":
        return k_residual_index(G)
    elif property == "order":
        return gp.number_of_nodes(G)
    elif property == "size":
        return gp.number_of_edges(G)
    elif property == "(order - domination_number)":
        return gp.number_of_nodes(G) - gp.domination_number(G)
    elif property == "(order - total_domination_number)":
        return gp.number_of_nodes(G) - gp.total_domination_number(G)
    elif property == "(order - connected_domination_number)":
        return gp.number_of_nodes(G) - gp.connected_domination_number(G)
    elif property == "(order - independence_number)":
        return gp.number_of_nodes(G) - gp.independence_number(G)
    elif property == "(order - power_domination_number)":
        return gp.number_of_nodes(G) - gp.power_domination_number(G)
    elif property == "(order - zero_forcing_number)":
        return gp.number_of_nodes(G) - gp.zero_forcing_number(G)
    elif property == "(order - diameter)":
        return gp.number_of_nodes(G) - gp.diameter(G)
    elif property == "(order - radius)":
        return gp.number_of_nodes(G) - gp.radius(G)
    elif property == "(order - triameter)":
        return gp.number_of_nodes(G) - gp.triameter(G)
    elif property == "(size - diameter)":
        return gp.number_of_edges(G) - gp.diameter(G)
    elif property == "(size - radius)":
        return gp.number_of_edges(G) - gp.radius(G)
    elif property == "(size - triameter)":
        return gp.number_of_edges(G) - gp.triameter(G)
    elif property == "(order - independent_domination_number)":
        return gp.number_of_nodes(G) - gp.independent_domination_number(G)
    elif property == "(order - chromatic_number)":
        return gp.number_of_nodes(G) - gp.chromatic_number(G)
    elif property == "(order - matching_number)":
        return gp.number_of_nodes(G) - gp.matching_number(G)
    elif property == "(order - min_maximal_matching_number)":
        return gp.number_of_nodes(G) - gp.min_maximal_matching_number(G)
    elif property == "(size - matching_number)":
        return gp.number_of_edges(G) - gp.matching_number(G)
    elif property == "(size - min_maximal_matching_number)":
        return gp.number_of_edges(G) - gp.min_maximal_matching_number(G)
    elif property == "(order - min_degree)":
        return gp.number_of_nodes(G) - gp.min_degree(G)
    elif property == "(order - max_degree)":
        return gp.number_of_nodes(G) - gp.max_degree(G)
    elif property == "(order - clique_number)":
        return gp.number_of_nodes(G) - gp.clique_number(G)
    elif property == "(order - residue)":
        return gp.number_of_nodes(G) - gp.residue(G)
    elif property == "(order - annihilation_number)":
        return gp.number_of_nodes(G) - gp.annihilation_number(G)
    elif property == "(order - sub_total_domination_number)":
        return gp.number_of_nodes(G) - gp.sub_total_domination_number(G)
    elif property == "(order - slater)":
        return gp.number_of_nodes(G) - gp.slater(G)
    elif property == "(order - k_slater_index)":
        return gp.number_of_nodes(G) - k_slater_index(G)
    elif property == "(order - k_residual_index)":
        return gp.number_of_nodes(G) - k_residual_index(G)
    elif property == "min_edge_cover":
        return len(gp.min_edge_cover(G))
    elif property == "[(annihilation_number + residue)/ max_degree]":
        return (gp.annihilation_number(G) + gp.residue(G)) / gp.max_degree(G)
    elif property == "[order/ max_degree]":
        return gp.number_of_nodes(G) / gp.max_degree(G)
    elif property == "[order/ (max_degree + 1)]":
        return gp.number_of_nodes(G) / (gp.max_degree(G) + 1)
    elif property == "[order/ (max_degree - 1)]":
        return gp.number_of_nodes(G) / (gp.max_degree(G) - 1)
    elif property == "[order/ (max_degree + 2)]":
        return gp.number_of_nodes(G) / (gp.max_degree(G) + 2)
    elif property == "(residue + annihilation_number)":
        return gp.residue(G) + gp.annihilation_number(G)
    elif property == "a connected graph":
        return gp.is_connected(G)
    elif property == "a connected and planar graph":
        return gp.is_connected(G) and gp.check_planarity(G)[0]
    elif property == "a connected and regular graph":
        return gp.is_connected(G) and gp.min_degree(G) == gp.max_degree(G)
    elif property == "a connected and cubic graph":
        return gp.is_connected(G) and gp.min_degree(G) == 3 and gp.max_degree(G) == 3
    elif property == "a connected graph which is not K_n":
        return gp.is_connected(G) and gp.is_isomorphic(G, gp.complete_graph(gp.number_of_nodes(G))) == False
    elif property == "a connected and triangle-free graph":
        return gp.is_connected(G) and set(gp.triangles(G).values()) == {0}
    elif property == "a connected and claw-free graph":
        return gp.is_connected(G) and gp.is_claw_free(G)
    elif property == "a connected and chordal graph":
        return gp.is_connected(G) and gp.is_chordal(G)
    elif property == "a tree graph":
        return gp.is_connected(G) and gp.is_tree(G)
    elif property == "a connected and at-free graph":
        return gp.is_connected(G) and gp.is_at_free(G)
    elif property == "an eulerian graph":
        return gp.is_connected(G) and gp.is_eulerian(G)
    elif property == "a connected and bipartite graph":
        return gp.is_connected(G) and gp.is_bipartite(G)
    elif property == "a connected graph with maximum degree at most 3":
        return gp.is_connected(G) and gp.max_degree(G) <= 3
    elif property == "a connected graph which is not K_n and has maximum degree at most 3":
        return gp.is_connected(G) and gp.is_isomorphic(G, gp.complete_graph(gp.number_of_nodes(G))) == False and gp.max_degree(G) <= 3
    elif property == "a connected and cubic graph which is not K_4":
        return gp.is_connected(G) and gp.is_isomorphic(G, gp.complete_graph(gp.number_of_nodes(G))) == False and gp.min_degree(G) == 3 and gp.max_degree(G) == 3
    elif property == "a connected, claw-free, and cubic graph":
        return gp.is_connected(G) and gp.min_degree(G) == 3 and gp.max_degree(G) == 3 and gp.is_claw_free(G)
    elif property == "a connected, planar, and cubic graph":
        return gp.is_connected(G) and gp.min_degree(G) == 3 and gp.max_degree(G) == 3 and gp.is_planar(G)
    elif property == "a connected graph with a total domination number equal to the domination number":
        return gp.is_connected(G) and gp.total_domination_number(G) == gp.domination_number(G)
    elif property == "a connected and well-covered graph":
        return gp.is_connected(G) and gp.independence_number(G) == gp.independent_domination_number(G)
    elif property == "a connected and Class-1 graph":
        new_G = gp.line_graph(G)
        return gp.is_connected(G) and gp.chromatic_number(new_G) == gp.max_degree(G)
    elif property == "a connected and Class-2 graph":
        new_G = gp.line_graph(G)
        return gp.is_connected(G) and gp.chromatic_number(new_G) == gp.max_degree(G) + 1
    elif property == "a connected graph with diameter at most 3":
        return gp.is_connected(G) and gp.diameter(G) <= 3
    elif property == "a connected and planar graph with diameter at most 3":
        return gp.is_connected(G) and gp.is_planar(G) and gp.diameter(G) <= 3
    elif property == "a connected_graph with min_degree at least 2":
        return gp.is_connected(G) and gp.min_degree(G) >= 2
    elif property == "a connected_graph with min_degree at least 3":
        return gp.is_connected(G) and gp.min_degree(G) >= 3
    elif property == "a connected_graph with min_degree at least 4":
        return gp.is_connected(G) and gp.min_degree(G) >= 4
    elif property == "a connected and bipartite graph with min_degree at least 2":
        return gp.is_connected(G) and gp.is_bipartite(G) and gp.min_degree(G) >= 2
    elif property == "a connected and bipartite graph with min_degree at least 3":
        return gp.is_connected(G) and gp.is_bipartite(G) and gp.min_degree(G) >= 3
    elif property == "a connected and bipartite graph with min_degree at least 4":
        return gp.is_connected(G) and gp.is_bipartite(G) and gp.min_degree(G) >= 4
    elif property == "a connected and planar graph with min_degree at least 2":
        return gp.is_connected(G) and gp.is_planar(G) and gp.min_degree(G) >= 2
    elif property == "a connected and planar graph with min_degree at least 3":
        return gp.is_connected(G) and gp.is_planar(G) and gp.min_degree(G) >= 3
    elif property == "a connected and planar graph with min_degree at least 4":
        return gp.is_connected(G) and gp.is_planar(G) and gp.min_degree(G) >= 4
    elif property == "a connected graph which is not K_n with min_degree at least 2":
        return gp.is_connected(G) and gp.is_isomorphic(G, gp.complete_graph(gp.number_of_nodes(G))) == False and gp.min_degree(G) >= 2
    elif property == "a connected graph which is not K_n with min_degree at least 3":
        return gp.is_connected(G) and gp.is_isomorphic(G, gp.complete_graph(gp.number_of_nodes(G))) == False and gp.min_degree(G) >= 3
    elif property == "a connected graph which is not K_n with min_degree at least 4":
        return gp.is_connected(G) and gp.is_isomorphic(G, gp.complete_graph(gp.number_of_nodes(G))) == False and gp.min_degree(G) >= 4
    elif property == "a connected and triangle-free graph with min_degree at least 2":
        return gp.is_connected(G) and set(gp.triangles(G).values()) == {0} and gp.min_degree(G) >= 2
    elif property == "a connected and triangle-free graph with min_degree at least 3":
        return gp.is_connected(G) and set(gp.triangles(G).values()) == {0} and gp.min_degree(G) >= 3
    elif property == "a connected and triangle-free graph with min_degree at least 4":
        return gp.is_connected(G) and set(gp.triangles(G).values()) == {0} and gp.min_degree(G) >= 4
    elif property == "a connected and at-free graph with min_degree at least 2":
        return gp.is_connected(G) and gp.is_at_free(G) and gp.min_degree(G) >= 2
    elif property == "a connected and at-free graph with min_degree at least 3":
        return gp.is_connected(G) and gp.is_at_free(G) and gp.min_degree(G) >= 3
    elif property == "a connected and at-free graph with min_degree at least 4":
        return gp.is_connected(G) and gp.is_at_free(G) and gp.min_degree(G) >= 4
    elif property == "a connected and claw-free graph with min_degree at least 2":
        return gp.is_connected(G) and gp.is_claw_free(G) and gp.min_degree(G) >= 2
    elif property == "a connected and claw-free graph with min_degree at least 3":
        return gp.is_connected(G) and gp.is_claw_free(G) and gp.min_degree(G) >= 3
    elif property == "a connected and claw-free graph with min_degree at least 4":
        return gp.is_connected(G) and gp.is_claw_free(G) and gp.min_degree(G) >= 4
    elif property == "a connected and chordal graph with min_degree at least 2":
        return gp.is_connected(G) and gp.is_chordal(G) and gp.min_degree(G) >= 2
    elif property == "a connected and chordal graph with min_degree at least 3":
        return gp.is_connected(G) and gp.is_chordal(G) and gp.min_degree(G) >= 3
    elif  property == "a connected graph with min_degree at least 2 and maximum degree at most 3":
        return gp.is_connected(G) and gp.min_degree(G) >= 2 and gp.max_degree(G) <= 3
    elif property == "a connected and diamond-free graph":
        return gp.is_connected(G) and is_diamond_free(G)
    elif property == "a connected, cubic, and diamond-free graph":
        return gp.is_connected(G) and is_cubic_and_diamond_free(G)
    elif property == "a connected and bull-free graph":
        return gp.is_connected(G) and gp.is_bull_free(G)
    else:
        return getattr(gp, property)(G)


def k_slater_index(G):
    """Return a the smallest integer k so that the sub-k-domination number
    of G is at least the domination number of G.
    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    Returns
    -------
    number
        The smallest ineteger k such that gp.domination_number(G) <= gp.sub_k_domination_number(G, k).
    """
    k = 1
    while gp.sub_k_domination_number(G, k) < gp.domination_number(G):
        k += 1
    return k

def vertex_cover_number(G):
    """Return a the size of smallest vertex cover in the graph G.
    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    Returns
    -------
    number
        The size of a smallest vertex cover of G.
    """
    return gp.number_of_nodes(G) - gp.independence_number(G)

def k_residual_index(G):
    """Return a the smallest integer k so that the k-residue of G is at least the
    independence number of G.
    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    Returns
    -------
    number
        The smallest ineteger k such that gp.independence_number(G) <= gp.k_residue(G, k).

    """
    k = 1
    while gp.k_residue(G, k) < gp.independence_number(G):
        k += 1
    return k

def is_diamond_free(G):
    """Return True if the graph G is diamond-free, and False otherwise.

    A graph is diamond-free if it does not contain a diamond as an induced subgraph.

    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.

    Returns
    -------
    bool
        True if G is diamond-free, and False otherwise.
    """
    diamond = gp.complete_graph(4)
    diamond.remove_edge(1, 2)
     # enumerate over all possible combinations of 5 vertices contained in G
    for S in set(itertools.combinations(G.nodes(), 4)):
        H = G.subgraph(list(S))
        if gp.is_isomorphic(H, diamond):
            return False
    # if the above loop completes, the graph is bull-free
    return True

def is_cubic_and_diamond_free(G):
    """Return True if the graph G is cubic and diamond-free, and False otherwise.

    A graph is cubic if every vertex has degree 3, and diamond-free if it does not contain a diamond as an induced subgraph.

    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.

    Returns
    -------
    bool
        True if G is cubic and diamond-free, and False otherwise.
    """
    return gp.min_degree(G) == gp.max_degree(G) == 3 and is_diamond_free(G)