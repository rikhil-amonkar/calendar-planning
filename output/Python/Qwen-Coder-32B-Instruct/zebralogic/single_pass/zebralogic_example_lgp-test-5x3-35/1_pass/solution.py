import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers_names = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(mothers_names)) * \
                       list(itertools.permutations(heights))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(names_perm, mothers_names_perm, heights_perm):
        # Unpack the permutations into more readable variables
        eric, peter, arnold, alice, bob = names_perm
        kailyn, janelle, aniya, penny, holly = mothers_names_perm
        average, very_short, short, very_tall, tall = heights_perm

        # Check each clue
        if alice != aniya:
            return False
        if heights_perm.index(average) >= heights_perm.index(penny):
            return False
        if janelle != bob:
            return False
        if peter == names[1]:
            return False
        if heights_perm.index(short) + 1 != names_perm.index(arnold):
            return False
        if very_tall != arnold:
            return False
        if heights_perm.index(average) - names_perm.index(bob) != 1:
            return False
        if eric == names[4]:
            return False
        if heights_perm.index(very_tall) <= mothers_names_perm.index(holly):
            return False
        if eric != kailyn:
            return False
        if very_short != names[4]:
            return False

        return True

    # Iterate over all possible combinations of permutations
    for names_perm in itertools.permutations(names):
        for mothers_names_perm in itertools.permutations(mothers_names):
            for heights_perm in itertools.permutations(heights):
                if is_valid_solution(names_perm, mothers_names_perm, heights_perm):
                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother's Name", "Height"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        solution["solution"]["rows"].append([
                            str(i + 1),
                            names_perm[i],
                            mothers_names_perm[i],
                            heights_perm[i]
                        ])
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())