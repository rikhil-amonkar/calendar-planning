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

    # Function to check if a permutation satisfies all the clues
    def is_valid(permutation):
        name1, name2 = permutation[0]
        sport1, sport2 = permutation[1]
        hobby1, hobby2 = permutation[2]

        # Clue 1: The person who enjoys gardening is Arnold.
        if hobby1 == "gardening" and name1 != "Arnold":
            return False
        if hobby2 == "gardening" and name2 != "Arnold":
            return False

        # Clue 2: The photography enthusiast is not in the first house.
        if hobby1 == "photography":
            return False

        # Clue 3: The person who loves soccer is not in the first house.
        if sport1 == "soccer":
            return False

        return True

    # Find the valid permutation
    for permutation in all_permutations:
        if is_valid(permutation):
            name1, name2 = permutation[0]
            sport1, sport2 = permutation[1]
            hobby1, hobby2 = permutation[2]
            solution = {
                "solution": {
                    "header": ["House", "Name", "FavoriteSport", "Hobby"],
                    "rows": [
                        [houses[0], name1, sport1, hobby1],
                        [houses[1], name2, sport2, hobby2]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())