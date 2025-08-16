import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]

    # Generate all possible permutations for names and hair colors
    for name_perm in itertools.permutations(names):
        for hair_perm in itertools.permutations(hair_colors):
            # Create a list of dictionaries representing each house
            assignment = [
                {"house": 1, "name": name_perm[0], "hair_color": hair_perm[0]},
                {"house": 2, "name": name_perm[1], "hair_color": hair_perm[1]},
                {"house": 3, "name": name_perm[2], "hair_color": hair_perm[2]},
                {"house": 4, "name": name_perm[3], "hair_color": hair_perm[3]}
            ]

            # Check all constraints
            if (assignment[2]["name"] == "Eric" and assignment[3]["hair_color"] == "blonde" and
                abs(assignment.index({"name": "Alice"}) - assignment.index({"name": "Arnold"})) == 1 and
                assignment[3]["name"] == "Eric" and assignment[3]["hair_color"] == "brown" and
                assignment[0]["hair_color"] != "black" and
                assignment[0]["name"] == "Alice"):
                
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor"],
                        "rows": [
                            [str(house), name, hair_color] for house, name, hair_color in zip(houses, name_perm, hair_perm)
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())