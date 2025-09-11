import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for hair_color_perm in itertools.permutations(hair_colors):
            # Unpack permutations for easier access
            name_map = {house: name for house, name in zip(houses, name_perm)}
            hair_color_map = {house: color for house, color in zip(houses, hair_color_perm)}

            # Check constraints
            if (name_map[1] == "Alice" and
                name_map[1] != name_map[2] and
                name_map[2] != name_map[3] and
                name_map[3] != name_map[4] and
                abs(name_perm.index("Alice") - name_perm.index("Arnold")) == 1 and
                name_map[hair_color_perm.index("blonde")] - 1 == name_map["Eric"] and
                name_map["Eric"] == hair_color_map["brown"] and
                hair_color_map["black"] != 1):
                
                # Construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor"],
                        "rows": [
                            [str(house), name_map[house], hair_color_map[house]] for house in houses
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())