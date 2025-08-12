import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    # Generate all possible permutations of assignments for the two houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(sports)) * \
                       list(itertools.permutations(hobbies))

    # Define the constraints
    def is_valid_solution(permutation):
        # Unpack the permutation into individual assignments
        (name1, name2), (sport1, sport2), (hobby1, hobby2) = permutation

        # Constraint 1: The person who enjoys gardening is Arnold.
        if hobby1 == "gardening" and name1 != "Arnold":
            return False
        if hobby2 == "gardening" and name2 != "Arnold":
            return False

        # Constraint 2: The photography enthusiast is not in the first house.
        if hobby1 == "photography":
            return False

        # Constraint 3: The person who loves soccer is not in the first house.
        if sport1 == "soccer":
            return False

        return True

    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            (name1, name2), (sport1, sport2), (hobby1, hobby2) = permutation
            solution = {
                "solution": {
                    "header": ["House", "Name", "Favorite Sport", "Hobby"],
                    "rows": [
                        ["1", name1, sport1, hobby1],
                        ["2", name2, sport2, hobby2]
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()