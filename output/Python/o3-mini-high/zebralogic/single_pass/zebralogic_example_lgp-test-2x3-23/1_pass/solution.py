#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the domains for each attribute
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    lunches = ["grilled cheese", "pizza"]

    solution = None

    # There are 2 houses: positions 1 (left) and 2 (right)
    # Each house has a unique Name, child, and lunch.
    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            for lunch_perm in itertools.permutations(lunches):
                # Assign attributes to houses:
                house1 = {"House": "1", "Name": name_perm[0], "child": child_perm[0], "lunch": lunch_perm[0]}
                house2 = {"House": "2", "Name": name_perm[1], "child": child_perm[1], "lunch": lunch_perm[1]}
                
                # Clue 2:
                # "The person who loves eating grilled cheese is directly left of the person's child is named Fred."
                # With two houses, house1 must have lunch "grilled cheese" and house2 must have child "Fred".
                if house1["lunch"] != "grilled cheese" or house2["child"] != "Fred":
                    continue

                # Clue 1:
                # "The person who is a pizza lover is Arnold."
                # So whichever house has lunch "pizza" must have Name "Arnold".
                if house1["lunch"] == "pizza" and house1["Name"] != "Arnold":
                    continue
                if house2["lunch"] == "pizza" and house2["Name"] != "Arnold":
                    continue

                # If all constraints are satisfied, we've found the solution.
                solution = [house1, house2]
                break
            if solution is not None:
                break
        if solution is not None:
            break

    if solution is None:
        result = {"solution": "No solution found"}
    else:
        # Construct the final result in the required JSON format.
        # The header must exactly match the attribute names: House, Name, child, lunch.
        result = {
            "solution": {
                "header": ["House", "Name", "child", "lunch"],
                "rows": [
                    [solution[0]["House"], solution[0]["Name"], solution[0]["child"], solution[0]["lunch"]],
                    [solution[1]["House"], solution[1]["Name"], solution[1]["child"], solution[1]["lunch"]]
                ]
            }
        }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()