import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]
    houses = [1, 2]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * list(itertools.permutations(children)) * list(itertools.permutations(foods))

    # Iterate over all possible combinations of permutations
    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            for food_perm in itertools.permutations(foods):
                # Create a list of dictionaries representing each house
                houses_list = [
                    {"House": 1, "Name": name_perm[0], "Children": child_perm[0], "Food": food_perm[0]},
                    {"House": 2, "Name": name_perm[1], "Children": child_perm[1], "Food": food_perm[1]}
                ]

                # Check the clues
                if (houses_list[0]["Name"] == "Arnold" and houses_list[0]["Food"] == "pizza") and \
                   (houses_list[0]["Food"] == "grilled cheese" and houses_list[1]["Children"] == "Fred"):
                    # If all clues are satisfied, format the solution as JSON
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Children", "Food"],
                            "rows": [
                                [str(houses_list[0]["House"]), houses_list[0]["Name"], houses_list[0]["Children"], houses_list[0]["Food"]],
                                [str(houses_list[1]["House"]), houses_list[1]["Name"], houses_list[1]["Children"], houses_list[1]["Food"]]
                            ]
                        }
                    }
                    return json.dumps(solution)

# Solve the puzzle and print the solution
print(solve_puzzle())