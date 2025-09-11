import itertools

# Define the lists
names = ["Alice", "Bob", "Charlie"]
birthdays = ["01-01", "02-14", "12-25"]
mothers = ["Mother1", "Mother2", "Mother3"]

# Generate permutations for each list
permutations_names = list(itertools.permutations(names))
permutations_birthdays = list(itertools.permutations(birthdays))
permutations_mothers = list(itertools.permutations(mothers))

# If you want to combine these permutations in some way, you can do so here.
# For example, if you want to create a Cartesian product of these permutations:
from itertools import product

combined_permutations = list(product(permutations_names, permutations_birthdays, permutations_mothers))

# Print the results
print("Permutations of names:")
for perm in permutations_names:
    print(perm)

print("\nPermutations of birthdays:")
for perm in permutations_birthdays:
    print(perm)

print("\nPermutations of mothers:")
for perm in permutations_mothers:
    print(perm)

print("\nCombined permutations:")
for combo in combined_permutations:
    print(combo)