import itertools
import json

# Define the possible values for each attribute
names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

# Generate all possible permutations for the attributes
permutations = list(itertools.permutations(names)) * 2
hair_permutations = list(itertools.permutations(hair_colors))
height_permutations = list(itertools.permutations(heights))

def is_valid_solution(solution):
    # Unpack the solution into separate lists
    names_sol = [house["Name"] for house in solution]
    hair_colors_sol = [house["HairColor"] for house in solution]
    heights_sol = [house["Height"] for house in solution]

    # Check each clue
    if hair_colors_sol.index("blonde") != names_sol.index("Bob") - 1:
        return False
    if names_sol[3] != "Alice":
        return False
    if heights_sol[names_sol.index("Arnold")] != "short":
        return False
    if heights_sol[5] != "tall":
        return False
    if hair_colors_sol[3] == "black":
        return False
    if hair_colors_sol[names_sol.index("Eric")] != "red":
        return False
    if heights_sol.index("super tall") <= heights_sol.index("average"):
        return False
    if hair_colors_sol[names_sol.index("Carol")] != "blonde":
        return False
    if abs(hair_colors_sol.index("gray") - hair_colors_sol.index("red")) != 2:
        return False
    if heights_sol[4] != "very short":
        return False
    if hair_colors_sol[names_sol.index("Bob")] != "brown":
        return False
    if hair_colors_sol[2] != "gray":
        return False
    if hair_colors_sol[names_sol.index("Carol")] != "blonde" or heights_sol[names_sol.index("Carol")] != "very tall":
        return False

    return True

# Iterate through all permutations to find the valid solution
for names_perm in permutations:
    for hair_perm in hair_permutations:
        for height_perm in height_permutations:
            solution = [
                {"House": str(i+1), "Name": names_perm[i], "HairColor": hair_perm[i], "Height": height_perm[i]}
                for i in range(6)
            ]
            if is_valid_solution(solution):
                # Convert to JSON format
                json_output = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "Height"],
                        "rows": [[house["House"], house["Name"], house["HairColor"], house["Height"]] for house in solution]
                    }
                }
                print(json.dumps(json_output, indent=2))
                exit()