import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
    heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for hair_color_perm in itertools.permutations(hair_colors):
            for height_perm in itertools.permutations(heights):
                # Create a list of dictionaries for each house
                houses_list = [
                    {"house": houses[i], "name": name_perm[i], "hair_color": hair_color_perm[i], "height": height_perm[i]}
                    for i in range(6)
                ]

                # Check all constraints
                if (houses_list[name_perm.index("Bob") - 1]["hair_color"] == "blonde" and
                    houses_list[3]["name"] == "Alice" and
                    houses_list[hair_color_perm.index("black")]["house"] != 4 and
                    houses_list[hair_color_perm.index("red")]["name"] == "Eric" and
                    houses_list[hair_color_perm.index("blonde")]["name"] == "Carol" and
                    abs(houses_list[hair_color_perm.index("gray")]["house"] - houses_list[hair_color_perm.index("red")]["house"]) == 2 and
                    houses_list[height_perm.index("short")]["name"] == "Arnold" and
                    houses_list[height_perm.index("tall")]["house"] == 6 and
                    houses_list[height_perm.index("very short")]["house"] == 5 and
                    houses_list[hair_color_perm.index("brown")]["name"] == "Bob" and
                    houses_list[hair_color_perm.index("gray")]["house"] == 3 and
                    houses_list[hair_color_perm.index("blonde")]["height"] == "very tall" and
                    height_perm.index("super tall") > height_perm.index("average")):

                    # If all constraints are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "Height"],
                            "rows": [
                                [str(house["house"]), house["name"], house["hair_color"], house["height"]]
                                for house in houses_list
                            ]
                        }
                    }

                    return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())