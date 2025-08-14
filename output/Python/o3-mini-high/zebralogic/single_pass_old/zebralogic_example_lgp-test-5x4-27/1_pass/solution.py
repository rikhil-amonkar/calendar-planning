#!/usr/bin/env python3
import itertools
import json

def main():
    names_possible = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays_possible = ["april", "feb", "mar", "jan", "sept"]
    cigars_possible = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks_possible = ["water", "coffee", "tea", "milk", "root beer"]

    solution = None

    # Iterate over possible assignments with fixed constraints.
    for names in itertools.permutations(names_possible):
        # Clue 13: Eric is in the third house (index 2)
        if names[2] != "Eric":
            continue
        # Clue 9: Arnold is directly left of Peter.
        if names.index("Arnold") + 1 != names.index("Peter"):
            continue

        for birthdays in itertools.permutations(birthdays_possible):
            # Clue 8: The person whose birthday is in February is in the second house.
            if birthdays[1] != "feb":
                continue
            # Clue 3: The person whose birthday is in April is Bob.
            if birthdays[names.index("Bob")] != "april":
                continue
            # Clue 6: There is one house between the person whose birthday is in January and Peter.
            if abs(birthdays.index("jan") - names.index("Peter")) != 2:
                continue

            for cigars in itertools.permutations(cigars_possible):
                # Clue 2: The person partial to Pall Mall is in the third house.
                if cigars[2] != "pall mall":
                    continue
                # Clue 7 (and 8): The person who smokes Blends is the person whose birthday is in February;
                # since February is in house 2, the blends smoker must be in house 2.
                if cigars[1] != "blends":
                    continue
                # Clue 4: The Dunhill smoker is the person whose birthday is in March.
                if birthdays[cigars.index("dunhill")] != "mar":
                    continue

                for drinks in itertools.permutations(drinks_possible):
                    # Clue 10: The person who likes milk is not in the fifth house.
                    if drinks[4] == "milk":
                        continue
                    # Clue 1: The root beer lover is Eric.
                    if drinks[names.index("Eric")] != "root beer":
                        continue
                    # Clue 5: Peter is somewhere to the right of the root beer lover.
                    if names.index("Peter") <= drinks.index("root beer"):
                        continue
                    # Clue 11: The person who smokes Blue Master is the coffee drinker.
                    blue_master_index = cigars.index("blue master")
                    if drinks[blue_master_index] != "coffee":
                        continue
                    coffee_index = drinks.index("coffee")
                    if cigars[coffee_index] != "blue master":
                        continue
                    # Clue 12: There is one house between the tea drinker and the coffee drinker.
                    if abs(drinks.index("tea") - drinks.index("coffee")) != 2:
                        continue

                    # All constraints are met; build the solution.
                    sol = []
                    for i in range(5):
                        house_number = str(i + 1)
                        sol.append([house_number, names[i], birthdays[i], cigars[i], drinks[i]])
                    solution = sol
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "birthday", "cigar", "drink"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()