import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names))
    permutations_children = list(itertools.permutations(children))
    permutations_smoothies = list(itertools.permutations(smoothies))

    # Iterate over all possible combinations
    for names_perm in permutations:
        for children_perm in permutations_children:
            for smoothies_perm in permutations_smoothies:
                # Unpack the permutations for easier access
                name1, name2, name3, name4, name5, name6 = names_perm
                child1, child2, child3, child4, child5, child6 = children_perm
                smoothie1, smoothie2, smoothie3, smoothie4, smoothie5, smoothie6 = smoothies_perm

                # Apply the clues
                if child3 == "Fred" and abs(names_perm.index("Desert") - 2) == 1:
                    if smoothies_perm.index("blueberry") < names_perm.index("Fred"):
                        if name3 != "Alice":
                            if child2 != "Samantha":
                                if smoothies_perm.index("watermelon") > smoothies_perm.index("cherry"):
                                    if child3 == "Alice" and smoothie3 == "watermelon":
                                        if name5 != "Samantha" and names_perm.index("Peter") > names_perm.index("Samantha"):
                                            if name2 != "Arnold":
                                                if child5 == "Timothy" and name5 == "Bob":
                                                    if names_perm.index("Arnold") + 1 == names_perm.index("Carol"):
                                                        if smoothies_perm.index("cherry") + 1 == names_perm.index("Samantha"):
                                                            if child6 == "Meredith" and smoothie6 == "dragonfruit":
                                                                # If all conditions are met, construct the solution
                                                                solution = {
                                                                    "solution": {
                                                                        "header": ["House", "Name", "Child", "Smoothie"],
                                                                        "rows": [
                                                                            ["1", name1, child1, smoothie1],
                                                                            ["2", name2, child2, smoothie2],
                                                                            ["3", name3, child3, smoothie3],
                                                                            ["4", name4, child4, smoothie4],
                                                                            ["5", name5, child5, smoothie5],
                                                                            ["6", name6, child6, smoothie6]
                                                                        ]
                                                                    }
                                                                }
                                                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())