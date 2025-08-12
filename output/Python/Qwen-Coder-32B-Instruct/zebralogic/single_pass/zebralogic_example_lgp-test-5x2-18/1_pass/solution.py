import itertools
import json

def solve_puzzle():
    # Define the attributes
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]
    houses = [1, 2, 3, 4, 5]

    # Generate all possible permutations for names and children
    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            # Unpack the permutations for easier access
            name_house_1, name_house_2, name_house_3, name_house_4, name_house_5 = name_perm
            child_house_1, child_house_2, child_house_3, child_house_4, child_house_5 = child_perm

            # Apply the constraints
            if (name_perm.index("Bob") < child_perm.index("Samantha") and
                name_perm.index(child_perm.index("Timothy")) < child_perm.index("Samantha") and
                child_house_2 == "Fred" and
                abs(name_perm.index(child_perm.index("Samantha")) - name_perm.index("Alice")) == 2 and
                name_house_3 != "Eric" and
                name_house_3 != "Bob" and
                child_house_2 == "Fred" and child_house_3 == "Bella" and
                child_perm.index("Samantha") < name_perm.index("Peter")):

                # Construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Child"],
                        "rows": [
                            ["1", name_house_1, child_house_1],
                            ["2", name_house_2, child_house_2],
                            ["3", name_house_3, child_house_3],
                            ["4", name_house_4, child_house_4],
                            ["5", name_house_5, child_house_5]
                        ]
                    }
                }

                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return

# Solve the puzzle
solve_puzzle()