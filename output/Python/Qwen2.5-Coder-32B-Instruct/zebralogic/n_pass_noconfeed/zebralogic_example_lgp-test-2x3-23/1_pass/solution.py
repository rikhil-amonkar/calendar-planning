import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]
    houses = [1, 2]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(children)) * \
                       list(itertools.permutations(foods))

    # Iterate through all permutations to find the correct one
    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            for food_perm in itertools.permutations(foods):
                # Create a list of dictionaries for each house
                houses_info = [
                    {"House": 1, "Name": name_perm[0], "Children": child_perm[0], "Food": food_perm[0]},
                    {"House": 2, "Name": name_perm[1], "Children": child_perm[1], "Food": food_perm[1]}
                ]

                # Check the clues
                # Clue 1: The person who is a pizza lover is Arnold.
                if not any(house["Name"] == "Arnold" and house["Food"] == "pizza" for house in houses_info):
                    continue

                # Clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
                if not (houses_info[0]["Food"] == "grilled cheese" and houses_info[1]["Children"] == "Fred"):
                    continue

                # If all clues are satisfied, return the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Children", "Food"],
                        "rows": [
                            [str(house["House"]), house["Name"], house["Children"], house["Food"]] for house in houses_info
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())