import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            # Create a dictionary to store the current permutation
            current_solution = {house: {"Name": name, "Height": height} for house, name, height in zip(houses, name_perm, height_perm)}

            # Check all constraints
            if (current_solution[2]["Height"] == "short" and
                name_perm.index("Peter") + 1 == name_perm.index("Bob") and
                name_perm.index("Eric") < name_perm.index("Peter") and
                name_perm.index("Peter") - 1 >= 0 and current_solution[name_perm.index("Peter") - 1 + 1]["Height"] == "very tall" and
                name_perm.index("Alice") + 1 < len(name_perm) and current_solution[name_perm.index("Alice") + 1 + 1]["Height"] == "average" and
                abs(name_perm.index("short") - name_perm.index("very short")) == 1 and
                current_solution[5]["Height"] == "average"):
                
                # Prepare the solution in the required format
                solution_rows = []
                for house in houses:
                    row = [str(house), current_solution[house]["Name"], current_solution[house]["Height"]]
                    solution_rows.append(row)

                solution_dict = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": solution_rows
                    }
                }

                # Output the solution as JSON
                print(json.dumps(solution_dict, indent=2))
                return

solve_puzzle()