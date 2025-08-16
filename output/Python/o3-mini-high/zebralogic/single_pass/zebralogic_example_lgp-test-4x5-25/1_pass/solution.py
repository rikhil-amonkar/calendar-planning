#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    names = ["Arnold", "Peter", "Eric", "Alice"]
    houseStyles = ["craftsman", "colonial", "victorian", "ranch"]
    hairColors = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    bookGenres = ["mystery", "fantasy", "romance", "science fiction"]

    # Iterate over all permutations, using fixed positions where possible.
    for perm_names in itertools.permutations(names):
        for perm_houseStyles in itertools.permutations(houseStyles):
            # Constraint 1: House 3 (index 2) must be "craftsman"
            if perm_houseStyles[2] != "craftsman":
                continue
            for perm_hairColors in itertools.permutations(hairColors):
                # Constraint 3: House 4 (index 3) hair must be "brown"
                # Constraint 9: House 2 (index 1) hair must be "black"
                if perm_hairColors[3] != "brown" or perm_hairColors[1] != "black":
                    continue
                for perm_children in itertools.permutations(children):
                    # Constraint 4: House 4 (index 3) child must be "Samantha"
                    if perm_children[3] != "Samantha":
                        continue
                    for perm_bookGenres in itertools.permutations(bookGenres):
                        valid = True
                        # Check person-specific constraints for each house
                        for i in range(4):
                            # Constraint 2: Alice loves romance books
                            if perm_names[i] == "Alice":
                                if perm_bookGenres[i] != "romance":
                                    valid = False
                                    break
                                # Constraint 8: Alice lives in a colonial-style house
                                if perm_houseStyles[i] != "colonial":
                                    valid = False
                                    break
                            # Constraint 10: Peter loves fantasy books
                            if perm_names[i] == "Peter":
                                if perm_bookGenres[i] != "fantasy":
                                    valid = False
                                    break
                                # Constraint 6: Peter's child is Bella
                                if perm_children[i] != "Bella":
                                    valid = False
                                    break
                            # Constraint 7: Arnold has red hair
                            if perm_names[i] == "Arnold":
                                if perm_hairColors[i] != "red":
                                    valid = False
                                    break
                                # Constraint 11: Arnold's child is Meredith
                                if perm_children[i] != "Meredith":
                                    valid = False
                                    break
                                # Constraint 13: Arnold loves science fiction books
                                if perm_bookGenres[i] != "science fiction":
                                    valid = False
                                    break
                            # Constraint 12: The person with black hair is Eric.
                            if perm_hairColors[i] == "black" and perm_names[i] != "Eric":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
                        try:
                            index_red = perm_hairColors.index("red")
                            index_ranch = perm_houseStyles.index("ranch")
                        except ValueError:
                            continue
                        if not (index_ranch > index_red):
                            continue

                        # Additional check from constraint 12: House 2 must be Eric (since it has black hair).
                        if perm_names[1] != "Eric":
                            continue

                        # If we reach here, all constraints are satisfied.
                        solution_rows = []
                        for i in range(4):
                            house_number = str(i + 1)
                            row = [
                                house_number,
                                perm_names[i],
                                perm_houseStyles[i],
                                perm_hairColors[i],
                                perm_children[i],
                                perm_bookGenres[i]
                            ]
                            solution_rows.append(row)

                        result = {
                            "solution": {
                                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(result))
                        sys.exit(0)

if __name__ == "__main__":
    main()