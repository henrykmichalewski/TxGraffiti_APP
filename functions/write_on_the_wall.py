from functions import (
    make_upper_linear_conjecture,
    make_lower_linear_conjecture,
    make_all_upper_linear_conjectures,
    make_all_lower_linear_conjectures,
    weak_dalmatian,
    strong_dalmatian,
    sort_conjectures,
    theo,
    filter_false_conjectures,
    make_more_general_conjectures,
    make_all_mip_linear_conjectures,
    make_upper_lower_mip_linear_conjecture,
)

from functions import (
    filter_conjectures,
    filter_by_inequalities,
    remove_zero_slopes,
)

__all__ = [
    "write_on_the_wall",
    "write_on_the_wall_with_mip",
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
        known_inequalities=[],
        known_conjectures=[],
        use_strong_dalmatian=False,
        make_upper_conjectures=True,
        make_lower_conjectures=True,
        type_two_conjectures=False,
    ):

    # if "a connected graph" not in boolean_columns:
    #     boolean_columns.append("a connected graph")

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
                    boolean_columns,
                )
            upper_conjectures = [conj for conj in upper_conjectures if conj.conclusion.slopes != [0, 0]]
            filtered_conjectures = [upper_conjectures[0]]
            for conj in upper_conjectures[1:]:
                if not any(conj == old_conj for old_conj in filtered_conjectures):
                    filtered_conjectures.append(conj)
            upper_conjectures = filtered_conjectures
        upper_conjectures = filter_false_conjectures(upper_conjectures, df)
        # upper_conjectures = make_more_general_conjectures(upper_conjectures, df)
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
                    boolean_columns,
                )
            lower_conjectures = [conj for conj in lower_conjectures if conj.conclusion.slopes != [0, 0]]
            filtered_conjectures = [lower_conjectures[0]]
            for conj in lower_conjectures[1:]:
                if not any(conj == old_conj for old_conj in filtered_conjectures):
                    filtered_conjectures.append(conj)
            lower_conjectures = filtered_conjectures
        lower_conjectures = filter_false_conjectures(lower_conjectures, df)
        # lower_conjectures = make_more_general_conjectures(lower_conjectures, df)
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


def write_on_the_wall_with_mip(
        df,
        target,
        numerical_columns,
        boolean_columns,
        known_inequalities=[],
        known_conjectures=[],
        use_strong_dalmatian=False,
        type_two_conjectures=False,
    ):

    upper_conjectures = []
    lower_conjectures = []
    equal_conjectures = []

    for other in numerical_columns:
        if other != target:
            for prop in boolean_columns:
                upper_conj, lower_conj = make_upper_lower_mip_linear_conjecture(df, target, [other], hyp=prop)
                if lower_conj:
                    upper_conjectures.append(upper_conj)
                    lower_conjectures.append(lower_conj)
                else:
                    equal_conjectures.append(upper_conj)

    if type_two_conjectures and len(boolean_columns) <= 3:
        new_numerical_columns = [column for column in numerical_columns if column not in DOUBLE_INVARIANTS]
        for other in new_numerical_columns:
            for prop in boolean_columns:
                upper_conj, lower_conj = make_upper_lower_mip_linear_conjecture(df, target, [other], hyp=prop)
                if lower_conj:
                    upper_conjectures.append(upper_conj)
                    lower_conjectures.append(lower_conj)
                else:
                    equal_conjectures.append(upper_conj)

    upper_conjectures = filter_false_conjectures(upper_conjectures, df)
    lower_conjectures = filter_false_conjectures(lower_conjectures, df)
    equal_conjectures = filter_false_conjectures(equal_conjectures, df)

    upper_conjectures = remove_zero_slopes(upper_conjectures)
    lower_conjectures = remove_zero_slopes(lower_conjectures)
    equal_conjectures = remove_zero_slopes(equal_conjectures)


    upper_conjectures = filter_by_inequalities(upper_conjectures, known_inequalities)
    lower_conjectures = filter_by_inequalities(lower_conjectures, known_inequalities)

    upper_conjectures = filter_conjectures(upper_conjectures, known_conjectures)
    lower_conjectures = filter_conjectures(lower_conjectures, known_conjectures)

    upper_conjectures = sort_conjectures(upper_conjectures)
    lower_conjectures = sort_conjectures(lower_conjectures)
    if upper_conjectures != []:
        if use_strong_dalmatian:
            upper_conjectures = strong_dalmatian(upper_conjectures)
            upper_conjectures = theo(upper_conjectures)
        else:
            upper_conjectures = weak_dalmatian(upper_conjectures)
            upper_conjectures = theo(upper_conjectures)
    if lower_conjectures != []:
        if use_strong_dalmatian:
            lower_conjectures = strong_dalmatian(lower_conjectures)
            lower_conjectures = theo(lower_conjectures)
        else:
            lower_conjectures = weak_dalmatian(lower_conjectures)
            lower_conjectures = theo(lower_conjectures)

    if equal_conjectures != []:
        equal_conjectures = theo(equal_conjectures)

    conjectures = lower_conjectures + upper_conjectures + equal_conjectures

    if conjectures != []:
        conjectures = sort_conjectures(conjectures, filter_touch=2)
    print(conjectures)
    return conjectures