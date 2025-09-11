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

    # Iterate over all possible combinations of permutations
    for perm_name in permutations:
        for perm_child in permutations_children:
            for perm_smoothie in permutations_smoothies:
                # Unpack the current permutation into variables
                name1, name2, name3, name4, name5, name6 = perm_name
                child1, child2, child3, child4, child5, child6 = perm_child
                smoothie1, smoothie2, smoothie3, smoothie4, smoothie5, smoothie6 = perm_smoothie

                # Check each clue
                if (child1 == "Fred" and smoothie2 == "desert") or (child2 == "Fred" and smoothie1 == "desert"):
                    if perm_smoothie.index("blueberry") < perm_child.index("Fred"):
                        if name3 != "Alice":
                            if child2 != "Samantha":
                                if perm_smoothie.index("watermelon") > perm_smoothie.index("cherry"):
                                    if child3 == "Alice" and name3 == "Alice" and smoothie3 == "watermelon":
                                        if perm_name.index("Peter") > perm_child.index("Samantha"):
                                            if name2 != "Arnold":
                                                if child5 == "Timothy" and name5 == "Bob":
                                                    if perm_name.index("Arnold") + 1 == perm_name.index("Carol"):
                                                        if perm_smoothie.index("cherry") + 1 == perm_child.index("Samantha"):
                                                            if child6 == "Meredith" and smoothie6 == "dragonfruit":
                                                                # If all conditions are met, construct the solution
                                                                solution = {
                                                                    "solution": {
                                                                        "header": ["House", "Name", "Children", "Smoothie"],
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

# Solve the puzzle and print the result
print(solve_puzzle())