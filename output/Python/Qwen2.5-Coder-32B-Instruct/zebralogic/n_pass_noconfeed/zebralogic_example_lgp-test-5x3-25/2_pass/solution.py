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
                # Create a dictionary to store the assignment
                assignment = {house: {"name": name, "height": height, "food": food}
                              for house, name, height, food in zip(houses, name_perm, height_perm, food_perm)}

                # Check constraints
                if (assignment[1]["name"] == "Alice" and assignment[1]["height"] == "short" and
                    assignment[3]["height"] == "tall" and
                    assignment[name_perm.index("Alice")]["height"] != "average" and
                    name_perm.index("Alice") < food_perm.index("stew") and
                    assignment[name_perm.index("Arnold")]["food"] == "stir fry" and
                    assignment[houses[height_perm.index("tall")]]["food"] == "pizza" and
                    assignment[name_perm.index("Eric")]["height"] == "tall" and
                    name_perm.index("Arnold") < name_perm.index("Bob") and
                    name_perm.index("Eric") < food_perm.index("grilled cheese") and
                    height_perm.index("very short") < name_perm.index("Arnold")):

                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Food"],
                            "rows": [[str(house), assignment[house]["name"], assignment[house]["height"], assignment[house]["food"]]
                                     for house in houses]
                        }
                    }

                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return

# Run the solver
solve_puzzle()