import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]

    # Generate all possible permutations for the attributes
    all_permutations = list(itertools.permutations(names))
    hair_permutations = list(itertools.permutations(hair_colors))

    # Function to check if a permutation satisfies all the clues
    def is_valid(names_perm, hair_perm):
        # Unpack the permutations for easier access
        name1, name2, name3, name4 = names_perm
        hair1, hair2, hair3, hair4 = hair_perm

        # Check each clue
        # Clue 1: Eric is directly left of the person who has blonde hair.
        if hair2 == "blonde" and name1 != "Eric":
            return False
        if hair3 == "blonde" and name2 != "Eric":
            return False
        if hair4 == "blonde" and name3 != "Eric":
            return False

        # Clue 2: Alice and Arnold are next to each other.
        if not (abs(names.index("Alice") - names.index("Arnold")) == 1):
            return False

        # Clue 3: Eric is the person who has brown hair.
        if names.index("Eric") != hair_perm.index("brown"):
            return False

        # Clue 4: The person who has black hair is not in the first house.
        if hair1 == "black":
            return False

        # Clue 5: Alice is in the first house.
        if name1 != "Alice":
            return False

        return True

    # Find the valid permutation
    for names_perm in all_permutations:
        for hair_perm in hair_permutations:
            if is_valid(names_perm, hair_perm):
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Hair Color"],
                        "rows": [
                            ["1", names_perm[0], hair_perm[0]],
                            ["2", names_perm[1], hair_perm[1]],
                            ["3", names_perm[2], hair_perm[2]],
                            ["4", names_perm[3], hair_perm[3]]
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())