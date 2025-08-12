import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["victorian", "ranch", "colonial", "craftsman"]

    # Generate all possible permutations for the assignments
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            # Unpack the permutations for easier access
            name1, name2, name3, name4 = name_perm
            style1, style2, style3, style4 = style_perm

            # Apply the clues to filter out invalid permutations
            if (name3 == "Eric" and style3 == "craftsman" and
                style2 == "ranch" and style1 == "victorian" and
                name4 == "Arnold" and name1 != "Alice" and
                style1 != "craftsman" and style2 != "craftsman" and
                style3 != "victorian" and style4 != "victorian" and
                name1 != "Eric" and name2 != "Eric" and
                name1 != "Arnold" and name2 != "Arnold" and name3 != "Arnold" and
                name1 != "Alice" and name2 != "Alice" and name3 != "Alice" and
                style1 != "ranch" and style3 != "ranch" and style4 != "ranch" and
                style2 != "victorian" and style3 != "victorian" and style4 != "victorian" and
                name1 == "Alice" if style1 == "victorian" else True and
                name2 == "Alice" if style2 == "victorian" else True and
                name3 == "Alice" if style3 == "victorian" else True and
                name4 == "Alice" if style4 == "victorian" else True):

                # Construct the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Style"],
                        "rows": [
                            ["1", name1, style1],
                            ["2", name2, style2],
                            ["3", name3, style3],
                            ["4", name4, style4]
                        ]
                    }
                }

                # Output the solution as a JSON-formatted string
                print(json.dumps(solution, indent=2))
                return

# Call the function to solve the puzzle
solve_puzzle()