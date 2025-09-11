all_permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(children)) * \
                   list(itertools.permutations(foods))