import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            for smoothie_perm in itertools.permutations(smoothies):
                # Unpack permutations for easier access
                name_map = dict(zip(houses, name_perm))
                child_map = dict(zip(houses, child_perm))
                smoothie_map = dict(zip(houses, smoothie_perm))

                # Apply constraints
                if (child_map[smoothie_perm.index("desert") + 1] == "Fred" or
                    child_map[smoothie_perm.index("desert") - 1] == "Fred"):
                    if smoothie_perm.index("blueberry") < smoothie_perm.index("desert"):
                        if name_map[5] != "Alice":
                            if child_map[2] != "Samantha":
                                if smoothie_perm.index("watermelon") > smoothie_perm.index("cherry"):
                                    if name_map[child_perm.index("Alice")] == "Alice":
                                        if smoothie_map[child_perm.index("Alice")] == "watermelon":
                                            if name_map.index("Peter") > name_map.index(child_perm.index("Samantha")):
                                                if name_map[2] != "Arnold":
                                                    if name_map[child_perm.index("Timothy")] == "Bob":
                                                        if name_map.index("Arnold") + 1 == name_map.index("Carol"):
                                                            if smoothie_perm.index("cherry") + 1 == name_map.index(child_perm.index("Samantha")):
                                                                if child_map[6] == "Meredith":
                                                                    if smoothie_map[6] == "dragonfruit":
                                                                        solution = {
                                                                            "solution": {
                                                                                "header": ["House", "Name", "Children", "Smoothie"],
                                                                                "rows": [
                                                                                    [str(house), name_map[house], child_map[house], smoothie_map[house]]
                                                                                    for house in houses
                                                                                ]
                                                                            }
                                                                        }
                                                                        return json.dumps(solution)

print(solve_puzzle())