#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    lunches = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    solutions = []
    
    # Iterate over all permutations of names, heights, and lunches
    for perm_names in itertools.permutations(names):
        # Clue 7 + Clue 2 combined: The person who is tall is in the third house and is Eric.
        # Thus, house 3 (index 2) must have the name Eric.
        if perm_names[2] != "Eric":
            continue

        for perm_heights in itertools.permutations(heights):
            # Clue 2: The person who is tall is in the third house.
            if perm_heights[2] != "tall":
                continue

            # Clue 1: Alice is the person who is short.
            valid = True
            for i in range(5):
                if perm_names[i] == "Alice" and perm_heights[i] != "short":
                    valid = False
                    break
            if not valid:
                continue

            # Clue 3: The person who has an average height is not in the second house.
            if perm_heights[1] == "average":
                continue

            for perm_lunches in itertools.permutations(lunches):
                # Clue 6: The person who is a pizza lover is the person who is tall.
                # Since the only tall is in house 3, house 3 must have pizza.
                if perm_lunches[2] != "pizza":
                    continue

                # Clue 5: The person who loves stir fry is Arnold.
                valid_arnold = True
                for i in range(5):
                    if perm_names[i] == "Arnold" and perm_lunches[i] != "stir fry":
                        valid_arnold = False
                        break
                if not valid_arnold:
                    continue

                # Clue 4: The person with average height is somewhere to the left of the person who loves stew.
                try:
                    index_average = perm_heights.index("average")
                    index_stew = perm_lunches.index("stew")
                except ValueError:
                    continue
                if not (index_average < index_stew):
                    continue

                # Clue 8: Bob is somewhere to the right of Arnold.
                index_arnold = perm_names.index("Arnold")
                index_bob = perm_names.index("Bob")
                if not (index_bob > index_arnold):
                    continue

                # Clue 9: The person who loves grilled cheese is somewhere to the right of Eric.
                index_grilled = perm_lunches.index("grilled cheese")
                index_eric = perm_names.index("Eric")  # This is index 2 since we forced it.
                if not (index_grilled > index_eric):
                    continue

                # Clue 10: The person who is very short is somewhere to the left of Arnold.
                index_very_short = perm_heights.index("very short")
                if not (index_very_short < index_arnold):
                    continue

                # If all constraints are satisfied, construct the solution
                solution_rows = []
                for i in range(5):
                    house_number = str(i + 1)
                    row = [house_number, perm_names[i], perm_heights[i], perm_lunches[i]]
                    solution_rows.append(row)
                solutions.append(solution_rows)

    # Assuming a unique solution, output the first one in JSON format.
    if solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Height", "Lunch"],
                "rows": solutions[0]
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()