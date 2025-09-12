n = 6  # Number of houses in the puzzle

# Example: Generate all possible permutations of house positions
import itertools

# Assume each house is labeled from 1 to n
house_positions = list(range(1, n + 1))

# Generate and print all permutations of the house positions
for perm in itertools.permutations(house_positions):
    print(perm)