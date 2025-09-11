import itertools

# Define the lists
names = ['Alice', 'Bob', 'Charlie']
children = ['David', 'Eve']
foods = ['Apple', 'Banana', 'Carrot']

# Generate all permutations for each list
all_permutations_names = list(itertools.permutations(names))
all_permutations_children = list(itertools.permutations(children))
all_permutations_foods = list(itertools.permutations(foods))

# Combine all permutations into a single list
all_permutations = all_permutations_names + all_permutations_children + all_permutations_foods

# Print the result (optional)
for perm in all_permutations:
    print(perm)