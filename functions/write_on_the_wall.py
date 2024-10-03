from functions import (
    make_upper_linear_conjecture,
    make_lower_linear_conjecture,
    make_all_upper_linear_conjectures,
    make_all_lower_linear_conjectures,
    weak_dalmatian,
    strong_dalmatian,
    sort_conjectures,
    theo,
)

from functions import (
    filter_conjectures,
    filter_by_inequalities,
    remove_zero_slopes,
)

__all__ = [
    "write_on_the_wall",
]

DOUBLE_INVARIANTS = [
    "(order - domination_number)",
    "(order - total_domination_number)",
    "(order - connected_domination_number)",
    "(order - power_domination_number)",
    "(order - zero_forcing_number)",
    "(order - triameter)",
    "(order - diameter)",
    "(order - radius)",
    "(order - independent_domination_number)",
    "(order - chromatic_number)",
    "(order - matching_number)",
    "(order - min_maximal_matching_number)",
    "(order - min_degree)",
    "(order - max_degree)",
    "(order - clique_number)",
    "(order - residue)",
    "(order - annihilation_number)",
    "(order - sub_total_domination_number)",
    "(order - slater)",
    "(order - k_slater_index)",
    "(order - k_residual_index)",
    "(residue + annihilation_number)",
]


def write_on_the_wall(
        df,
        target,
        numerical_columns,
        boolean_columns,
        known_inequalities,
        known_conjectures,
        use_strong_dalmatian=False,
        make_upper_conjectures=True,
        make_lower_conjectures=True,
        type_two_conjectures=False,
    ):

    if "a connected graph" not in boolean_columns:
        boolean_columns.append("a connected graph")

    # # print(numerical_columns)
    upper_conjectures = []
    if make_upper_conjectures:
        for other in numerical_columns:
            if other != target:
                upper_conjectures += make_all_upper_linear_conjectures(
                    df,
                    target,
                    [other],
                    boolean_columns,
                )
        if type_two_conjectures and len(boolean_columns) <= 3:
            new_numerical_columns = [column for column in numerical_columns if column not in DOUBLE_INVARIANTS]
            upper_conjectures += make_all_upper_linear_conjectures(
                    df,
                    target,
                    new_numerical_columns,
                    ["a connected graph"],
                )
            upper_conjectures = [conj for conj in upper_conjectures if conj.conclusion.slopes != [0, 0]]
            filtered_conjectures = [upper_conjectures[0]]
            for conj in upper_conjectures[1:]:
                if not any(conj == old_conj for old_conj in filtered_conjectures):
                    filtered_conjectures.append(conj)
            upper_conjectures = filtered_conjectures
        upper_conjectures = remove_zero_slopes(upper_conjectures)
        upper_conjectures = filter_by_inequalities(upper_conjectures, known_inequalities)
        upper_conjectures = filter_conjectures(upper_conjectures, known_conjectures)
        upper_conjectures = sort_conjectures(upper_conjectures)

        if use_strong_dalmatian:
            upper_conjectures = strong_dalmatian(upper_conjectures)
        else:
            upper_conjectures = weak_dalmatian(upper_conjectures)
        upper_conjectures = theo(upper_conjectures)

    lower_conjectures = []
    if make_lower_conjectures:
        for other in numerical_columns:
            if other != target:
                lower_conjectures += make_all_lower_linear_conjectures(
                    df,
                    target,
                    [other],
                    boolean_columns,
                )
        if type_two_conjectures and len(boolean_columns) <= 3:
            new_numerical_columns = [column for column in numerical_columns if column not in DOUBLE_INVARIANTS]
            lower_conjectures += make_all_lower_linear_conjectures(
                    df,
                    target,
                    new_numerical_columns,
                    ["a connected graph"],
                )
            lower_conjectures = [conj for conj in lower_conjectures if conj.conclusion.slopes != [0, 0]]
            filtered_conjectures = [lower_conjectures[0]]
            for conj in lower_conjectures[1:]:
                if not any(conj == old_conj for old_conj in filtered_conjectures):
                    filtered_conjectures.append(conj)
            lower_conjectures = filtered_conjectures
        lower_conjectures = remove_zero_slopes(lower_conjectures)
        lower_conjectures = filter_by_inequalities(lower_conjectures, known_inequalities)
        lower_conjectures = filter_conjectures(lower_conjectures, known_conjectures)

        lower_conjectures = sort_conjectures(lower_conjectures)
        if use_strong_dalmatian:
            lower_conjectures = strong_dalmatian(lower_conjectures)
        else:
            lower_conjectures = weak_dalmatian(lower_conjectures)
        lower_conjectures = theo(lower_conjectures)

    conjectures = lower_conjectures + upper_conjectures
    conjectures = sort_conjectures(conjectures)
    return conjectures