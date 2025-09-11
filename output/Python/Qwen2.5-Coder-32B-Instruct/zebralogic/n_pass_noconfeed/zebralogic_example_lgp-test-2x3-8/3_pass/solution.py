import itertools

all_permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(birthdays)) * \
                   list(itertools.permutations(mothers))