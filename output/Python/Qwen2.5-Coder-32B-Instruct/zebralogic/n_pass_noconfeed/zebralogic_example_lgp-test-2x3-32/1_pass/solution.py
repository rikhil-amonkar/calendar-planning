import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]
    houses = [1, 2]

    # Generate all possible permutations for the assignments
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(colors))

    # Check each permutation against the clues
    for name_perm in itertools.permutations(names):
        for birthday_perm in itertools.permutations(birthdays):
            for color_perm in itertools.permutations(colors):
                # Unpack the permutations
                name1, name2 = name_perm
                birthday1, birthday2 = birthday_perm
                color1, color2 = color_perm

                # Apply the clues
                if (name1 == "Eric" and color1 == "yellow") or \
                   (name2 == "Eric" and color2 != "yellow") or \
                   (birthday1 != "april") or \
                   (color1 == "yellow"):
                    continue

                # If all clues are satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Color"],
                        "rows": [
                            [str(houses[0]), name1, birthday1, color1],
                            [str(houses[1]), name2, birthday2, color2]
                        ]
                    }
                }

                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return

# Run the solver
solve_puzzle()