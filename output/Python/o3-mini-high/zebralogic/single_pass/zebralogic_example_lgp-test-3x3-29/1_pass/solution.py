#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the attributes for each category
    names = ["Eric", "Peter", "Arnold"]
    mothers = ["Holly", "Aniya", "Janelle"]
    lunches = ["pizza", "grilled cheese", "spaghetti"]

    solution = None

    # Houses are numbered 1 to 3 (index 0 -> House 1, etc.)
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for lunch_perm in itertools.permutations(lunches):
                houses = []
                for i in range(3):
                    houses.append({
                        "House": str(i + 1),
                        "Name": name_perm[i],
                        "Mother": mother_perm[i],
                        "Lunch": lunch_perm[i]
                    })
                valid = True

                # Constraint 3: The person who loves eating grilled cheese is Eric.
                grilled_index = None
                for i, house in enumerate(houses):
                    if house["Lunch"] == "grilled cheese":
                        grilled_index = i
                        if house["Name"] != "Eric":
                            valid = False
                        break
                if grilled_index is None:
                    valid = False

                # Constraint 2: The person who loves eating grilled cheese is directly left of the person whose mother's name is Aniya.
                if valid:
                    if grilled_index < 2:
                        if houses[grilled_index + 1]["Mother"] != "Aniya":
                            valid = False
                    else:
                        valid = False

                # Constraint 4: Peter is the person whose mother's name is Holly.
                if valid:
                    for house in houses:
                        if house["Name"] == "Peter":
                            if house["Mother"] != "Holly":
                                valid = False
                            break

                # Constraint 1: The person who loves spaghetti and Peter are next to each other.
                if valid:
                    spaghetti_index = None
                    peter_index = None
                    for i, house in enumerate(houses):
                        if house["Lunch"] == "spaghetti":
                            spaghetti_index = i
                        if house["Name"] == "Peter":
                            peter_index = i
                    if spaghetti_index is None or peter_index is None or abs(spaghetti_index - peter_index) != 1:
                        valid = False

                if valid:
                    solution = houses
                    break
            if solution:
                break
        if solution:
            break

    # Prepare output in the required JSON format
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Lunch"],
            "rows": []
        }
    }

    if solution:
        # The houses are already in order (House 1, 2, 3)
        for house in solution:
            row = [house["House"], house["Name"], house["Mother"], house["Lunch"]]
            output["solution"]["rows"].append(row)

    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()