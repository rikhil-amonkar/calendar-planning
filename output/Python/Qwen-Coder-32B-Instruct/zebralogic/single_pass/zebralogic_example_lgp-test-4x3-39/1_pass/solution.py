import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]

    # Generate all possible permutations for each attribute
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(hair_colors)) * \
                   list(itertools.permutations(sports))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names_perm, hair_colors_perm, sports_perm):
        # Unpack the permutations into separate lists
        name1, name2, name3, name4 = names_perm
        hair1, hair2, hair3, hair4 = hair_colors_perm
        sport1, sport2, sport3, sport4 = sports_perm

        # Apply the clues
        if sport2 == "soccer":
            return False
        if name1 != "Eric" and name2 != "Eric" and name3 != "Eric" and name4 != "Eric":
            return False
        if hair1 == "blonde" and not (hair2 == "blonde" or hair3 == "blonde" or hair4 == "blonde"):
            return False
        if hair1 != "blonde" and hair2 != "blonde" and hair3 != "blonde" and hair4 != "blonde":
            return False
        if hair1 == "blonde" and not (sport1 == "basketball" or sport2 == "basketball" or sport3 == "basketball"):
            return False
        if hair2 == "blonde" and not (sport1 == "basketball" or sport3 == "basketball" or sport4 == "basketball"):
            return False
        if hair3 == "blonde" and not (sport1 == "basketball" or sport2 == "basketball" or sport4 == "basketball"):
            return False
        if hair4 == "blonde" and not (sport1 == "basketball" or sport2 == "basketball" or sport3 == "basketball"):
            return False
        if hair1 != "black" and hair2 != "black" and hair3 != "black" and hair4 != "black":
            return False
        if sport1 != "tennis" and sport2 != "tennis" and sport3 != "tennis" and sport4 != "tennis":
            return False
        if hair1 == "black" and sport1 != "tennis":
            return False
        if hair2 == "black" and sport2 != "tennis":
            return False
        if hair3 == "black" and sport3 != "tennis":
            return False
        if hair4 == "black" and sport4 != "tennis":
            return False
        if name1 != "Arnold" and name2 != "Arnold" and name3 != "Arnold" and name4 != "Arnold":
            return False
        if hair1 != "red" and hair2 != "red" and hair3 != "red" and hair4 != "red":
            return False
        if name1 == "Arnold" and not (hair2 == "red" or hair3 == "red" or hair4 == "red"):
            return False
        if name2 == "Arnold" and not (hair3 == "red" or hair4 == "red"):
            return False
        if name3 == "Arnold" and not (hair4 == "red"):
            return False
        if name4 == "Arnold":
            return False
        if name1 != "Alice" and name2 != "Alice" and name3 != "Alice" and name4 != "Alice":
            return False
        if sport1 != "swimming" and sport2 != "swimming" and sport3 != "swimming" and sport4 != "swimming":
            return False
        if name1 == "Alice" and sport1 != "swimming":
            return False
        if name2 == "Alice" and sport2 != "swimming":
            return False
        if name3 == "Alice" and sport3 != "swimming":
            return False
        if name4 == "Alice" and sport4 != "swimming":
            return False
        if hair1 != "red" and hair2 != "red" and hair3 != "red" and hair4 != "red":
            return False
        if hair1 != "black" and hair2 != "black" and hair3 != "black" and hair4 != "black":
            return False
        if hair2 == "red" and hair1 != "black":
            return False
        if hair3 == "red" and hair2 != "black":
            return False
        if hair4 == "red" and hair3 != "black":
            return False

        return True

    # Iterate through all combinations of permutations
    for names_perm in itertools.permutations(names):
        for hair_colors_perm in itertools.permutations(hair_colors):
            for sports_perm in itertools.permutations(sports):
                if is_valid_solution(names_perm, hair_colors_perm, sports_perm):
                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hair Color", "Favorite Sport"],
                            "rows": [
                                ["1", names_perm[0], hair_colors_perm[0], sports_perm[0]],
                                ["2", names_perm[1], hair_colors_perm[1], sports_perm[1]],
                                ["3", names_perm[2], hair_colors_perm[2], sports_perm[2]],
                                ["4", names_perm[3], hair_colors_perm[3], sports_perm[3]]
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())