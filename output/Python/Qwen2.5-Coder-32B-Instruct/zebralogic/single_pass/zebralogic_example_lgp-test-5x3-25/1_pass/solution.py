import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for food_perm in itertools.permutations(foods):
                # Unpack permutations for easier access
                name_map = dict(zip(houses, name_perm))
                height_map = dict(zip(houses, height_perm))
                food_map = dict(zip(houses, food_perm))

                # Check all constraints
                if (name_map[height_map.index("short")] == "Alice" and
                    height_map[3] == "tall" and
                    height_map.index("average") != 2 and
                    height_map.index("average") < food_map.index("stew") and
                    name_map[food_map.index("stir fry")] == "Arnold" and
                    height_map[food_map.index("pizza")] == "tall" and
                    name_map[height_map.index("tall")] == "Eric" and
                    name_map.index("Arnold") < name_map.index("Bob") and
                    name_map.index("Eric") < food_map.index("grilled cheese") and
                    height_map.index("very short") < name_map.index("Arnold")):

                    # If all constraints are satisfied, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Food"],
                            "rows": [
                                [str(house), name_map[house], height_map[house], food_map[house]]
                                for house in houses
                            ]
                        }
                    }

                    return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())