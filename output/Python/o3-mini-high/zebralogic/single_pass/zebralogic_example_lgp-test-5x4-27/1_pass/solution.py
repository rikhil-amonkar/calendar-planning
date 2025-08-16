#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the lists of attributes.
    names_list = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays_list = ["april", "feb", "mar", "jan", "sept"]
    cigars_list = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks_list = ["water", "coffee", "tea", "milk", "root beer"]

    solution = None

    # Iterate over all permutations subject to fixed positional constraints.
    for names in itertools.permutations(names_list):
        # Clue 13: Eric is in the third house (index 2).
        if names[2] != "Eric":
            continue
        # Clue 9 and Clue 5 force that Peter must be to the right of the house with root beer and
        # Arnold must be immediately left of Peter. Given Eric is fixed in house 3, Peter cannot be in house 3.
        # Later constraints will force Peter to be at house5 and Arnold at house4.
        for birthdays in itertools.permutations(birthdays_list):
            # Clue 8: The person with birthday in February is in the second house (index 1).
            if birthdays[1] != "feb":
                continue
            for cigars in itertools.permutations(cigars_list):
                # Clue 2: Pall Mall is in the third house (index 2).
                if cigars[2] != "pall mall":
                    continue
                # Clue 7: The person who smokes Blends must have birthday February.
                # Since birthday feb is fixed at house2 (index 1) use that:
                if cigars[1] != "blends":
                    continue
                for drinks in itertools.permutations(drinks_list):
                    # Clue 1: The root beer drinker is Eric.
                    # Clue 13 gives Eric in house 3 (index 2), so his drink must be root beer.
                    if drinks[2] != "root beer":
                        continue
                    # Clue 10: The person who likes milk is not in the fifth house (index 4).
                    if drinks[4] == "milk":
                        continue

                    valid = True

                    # Clue 3: The person whose birthday is in April is Bob.
                    for i in range(5):
                        if birthdays[i] == "april" and names[i] != "Bob":
                            valid = False
                            break
                        if names[i] == "Bob" and birthdays[i] != "april":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 4: The Dunhill smoker is the person whose birthday is in March.
                    for i in range(5):
                        if cigars[i] == "dunhill" and birthdays[i] != "mar":
                            valid = False
                            break
                        if birthdays[i] == "mar" and cigars[i] != "dunhill":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 7 (biconditional): If someone smokes Blends, then their birthday is february.
                    for i in range(5):
                        if cigars[i] == "blends" and birthdays[i] != "feb":
                            valid = False
                            break
                        if birthdays[i] == "feb" and cigars[i] != "blends":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 11: The person who smokes Blue Master is the coffee drinker.
                    for i in range(5):
                        if cigars[i] == "blue master" and drinks[i] != "coffee":
                            valid = False
                            break
                        if drinks[i] == "coffee" and cigars[i] != "blue master":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 5: Peter is somewhere to the right of the root beer lover.
                    # Root beer is only once and must be with Eric, who is in house 3 (index 2) so Peter must be in a house >2.
                    try:
                        pos_peter = names.index("Peter")
                        pos_rootbeer = drinks.index("root beer")
                    except ValueError:
                        valid = False
                    if pos_peter <= pos_rootbeer:
                        valid = False
                    if not valid:
                        continue

                    # Clue 6: There is one house between the person whose birthday is in January and Peter.
                    try:
                        pos_jan = birthdays.index("jan")
                    except ValueError:
                        valid = False
                    if abs(pos_jan - pos_peter) != 2:
                        valid = False
                    if not valid:
                        continue

                    # Clue 9: Arnold is directly left of Peter.
                    try:
                        pos_arnold = names.index("Arnold")
                    except ValueError:
                        valid = False
                    if pos_arnold + 1 != pos_peter:
                        valid = False
                    if not valid:
                        continue

                    # Clue 12: There is one house between the tea drinker and the coffee drinker.
                    try:
                        pos_tea = drinks.index("tea")
                        pos_coffee = drinks.index("coffee")
                    except ValueError:
                        valid = False
                    if abs(pos_tea - pos_coffee) != 2:
                        valid = False
                    if not valid:
                        continue

                    # If all constraints are satisfied, we have found the solution.
                    rows = []
                    for i in range(5):
                        # House numbers as strings ("1" for index 0, etc.)
                        rows.append([str(i+1), names[i], birthdays[i], cigars[i], drinks[i]])
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                            "rows": rows
                        }
                    }
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    # If no solution is found, return an empty rows list.
    if solution is None:
        solution = {"solution": {"header": ["House", "Name", "Birthday", "Cigar", "Drink"], "rows": []}}

    # Output the solution as valid JSON.
    print(json.dumps(solution))

if __name__ == "__main__":
    main()