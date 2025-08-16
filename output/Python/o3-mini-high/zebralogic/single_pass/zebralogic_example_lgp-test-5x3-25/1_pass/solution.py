#!/usr/bin/env python3
import itertools
import json

def main():
    names_all = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights_all = ["very tall", "average", "tall", "very short", "short"]
    foods_all = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    solution = None

    # Houses are numbered 1 to 5, but we use list index 0-4.
    # Fixed constraints:
    # - House 3 (index 2) must have "Eric" and height "tall", and then food "pizza" (by clues 2, 7, 6)
    for names in itertools.permutations(names_all):
        if names[2] != "Eric":
            continue
        for heights in itertools.permutations(heights_all):
            if heights[2] != "tall":
                continue
            for foods in itertools.permutations(foods_all):
                if foods[2] != "pizza":
                    continue

                valid = True

                # Clue 1: Alice is the person who is short.
                for i in range(5):
                    if names[i] == "Alice" and heights[i] != "short":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 3: The person who has an average height is not in the second house.
                if heights[1] == "average":
                    continue

                # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew.
                try:
                    avg_index = heights.index("average")
                    stew_index = foods.index("stew")
                except ValueError:
                    continue
                if not (avg_index < stew_index):
                    continue

                # Clue 5: The person who loves stir fry is Arnold.
                arnold_index = names.index("Arnold")
                if foods[arnold_index] != "stir fry":
                    continue

                # Clue 8: Bob is somewhere to the right of Arnold.
                bob_index = names.index("Bob")
                if not (bob_index > arnold_index):
                    continue

                # Clue 9: The person who loves eating grilled cheese is somewhere to the right of Eric (house 3, index 2).
                grilled_index = foods.index("grilled cheese")
                if not (grilled_index > 2):
                    continue

                # Clue 10: The person who is very short is somewhere to the left of Arnold.
                very_short_index = heights.index("very short")
                if not (very_short_index < arnold_index):
                    continue

                # If all constraints are satisfied, record the solution.
                solution = {
                    "houses": [
                        {"House": "1", "Name": names[0], "Height": heights[0], "Food": foods[0]},
                        {"House": "2", "Name": names[1], "Height": heights[1], "Food": foods[1]},
                        {"House": "3", "Name": names[2], "Height": heights[2], "Food": foods[2]},
                        {"House": "4", "Name": names[3], "Height": heights[3], "Food": foods[3]},
                        {"House": "5", "Name": names[4], "Height": heights[4], "Food": foods[4]}
                    ]
                }
                break
            if solution is not None:
                break
        if solution is not None:
            break

    # Prepare output JSON object with the required structure.
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Height", "Food"], "rows": []}}
    else:
        rows = []
        for house in solution["houses"]:
            rows.append([house["House"], house["Name"], house["Height"], house["Food"]])
        output = {"solution": {"header": ["House", "Name", "Height", "Food"], "rows": rows}}

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()