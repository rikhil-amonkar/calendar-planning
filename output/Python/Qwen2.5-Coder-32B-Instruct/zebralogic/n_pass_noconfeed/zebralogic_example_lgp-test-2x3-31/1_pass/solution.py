import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]
    houses = ["1", "2"]

    # Generate all possible permutations for the assignments
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(sports)) * \
                       list(itertools.permutations(hobbies))

    # Define the constraints
    def is_valid_solution(perm):
        name_perm, sport_perm, hobby_perm = perm[0], perm[1], perm[2]
        # Constraint 1: The person who enjoys gardening is Arnold.
        if hobby_perm[houses.index("1")] == "gardening" and name_perm[houses.index("1")] != "Arnold":
            return False
        if hobby_perm[houses.index("2")] == "gardening" and name_perm[houses.index("2")] != "Arnold":
            return False
        # Constraint 2: The photography enthusiast is not in the first house.
        if hobby_perm[houses.index("1")] == "photography":
            return False
        # Constraint 3: The person who loves soccer is not in the first house.
        if sport_perm[houses.index("1")] == "soccer":
            return False
        return True

    # Find the valid solution
    for perm in all_permutations:
        if is_valid_solution(perm):
            name_perm, sport_perm, hobby_perm = perm[0], perm[1], perm[2]
            solution = {
                "solution": {
                    "header": ["House", "Name", "FavoriteSport", "Hobby"],
                    "rows": [
                        [houses[0], name_perm[0], sport_perm[0], hobby_perm[0]],
                        [houses[1], name_perm[1], sport_perm[1], hobby_perm[1]]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Execute the function and print the result
print(solve_puzzle())