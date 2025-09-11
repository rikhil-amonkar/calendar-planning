import itertools

names = [...]  # Make sure to define the 'names' list
children = [...]  # Make sure to define the 'children' list
foods = [...]  # Make sure to define the 'foods' list

all_permutations = list(itertools.permutations(names)) + \
                   list(itertools.permutations(children)) + \
                   list(itertools.permutations(foods))