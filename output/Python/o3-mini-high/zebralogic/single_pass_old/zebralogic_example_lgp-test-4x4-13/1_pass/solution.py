#!/usr/bin/env python3
import itertools
import json

def main():
    # Define possible attributes for each category
    names_list = ["Alice", "Peter", "Arnold", "Eric"]
    cigars_list = ["prince", "dunhill", "blue master", "pall mall"]
    sports_list = ["swimming", "basketball", "soccer", "tennis"]
    drinks_list = ["coffee", "water", "milk", "tea"]
    
    solution = None

    # There are 4 houses, index 0 to 3 corresponding to houses 1..4.
    # We use brute force with permutations for the 4 categories.
    # We'll impose constraints from the puzzle:
    #
    # Clue 1: Peter is in the fourth house => names[3] == "Peter"
    # Clue 7: The coffee drinker is Arnold => drinks[ index_of("Arnold") ] == "coffee"
    # Clue 6: There are two houses between the one who only drinks water and Peter.
    #          That means abs(index_of("water") - index_of("Peter")) == 3.
    # Clue 8: The person who loves basketball is in the third house => sports[2] == "basketball"
    # Clue 4: The person who loves basketball is Eric => the house with "basketball" in sports must have name "Eric"
    # Clue 2: The tea drinker is the person who loves basketball => in the house with basketball, drink is "tea"
    # Clue 3: Arnold is the person who smokes Blue Master => cigar at house of "Arnold" == "blue master"
    # Clue 5: The person who loves tennis is the person who smokes Blue Master => for house i, if sports[i]=="tennis" then cigars[i]=="blue master"
    # Clue 9: The Prince smoker is the person who loves soccer => for house i, if cigars[i]=="prince" then sports[i]=="soccer"
    # Clue 10: Peter is the person partial to Pall Mall => cigar at house of "Peter" == "pall mall"

    for names in itertools.permutations(names_list):
        # Clue 1: Peter is in the fourth house (index 3)
        if names[3] != "Peter":
            continue

        for drinks in itertools.permutations(drinks_list):
            # Clue 6: There are two houses between the one who only drinks water and Peter.
            try:
                water_house = drinks.index("water")
            except ValueError:
                continue
            peter_house = names.index("Peter")
            if abs(water_house - peter_house) != 3:
                continue

            for sports in itertools.permutations(sports_list):
                # Clue 8: The person who loves basketball is in the third house (index 2)
                if sports[2] != "basketball":
                    continue
                # Clue 4: The person who loves basketball is Eric.
                basketball_house = sports.index("basketball")
                if names[basketball_house] != "Eric":
                    continue
                # Clue 2: The tea drinker is the person who loves basketball.
                if drinks[basketball_house] != "tea":
                    continue

                for cigars in itertools.permutations(cigars_list):
                    valid = True

                    # Clue 3: Arnold is the person who smokes Blue Master.
                    try:
                        arnold_house = names.index("Arnold")
                    except ValueError:
                        valid = False
                    else:
                        if cigars[arnold_house] != "blue master":
                            valid = False

                    if not valid:
                        continue

                    # Clue 7: The coffee drinker is Arnold.
                    if drinks[arnold_house] != "coffee":
                        continue

                    # Clue 5: The person who loves tennis is the person who smokes Blue Master.
                    # There is exactly one house with tennis; check that house's cigar is Blue Master.
                    try:
                        tennis_house = sports.index("tennis")
                    except ValueError:
                        continue
                    if cigars[tennis_house] != "blue master":
                        continue

                    # Clue 10: Peter is the person partial to Pall Mall.
                    try:
                        peter_house = names.index("Peter")
                    except ValueError:
                        continue
                    if cigars[peter_house] != "pall mall":
                        continue

                    # Clue 9: The Prince smoker is the person who loves soccer.
                    try:
                        prince_house = cigars.index("prince")
                    except ValueError:
                        continue
                    if sports[prince_house] != "soccer":
                        continue

                    # All constraints satisfied; record the solution.
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "favorite cigar", "favorite sport", "favorite drink"],
                            "rows": []
                        }
                    }
                    # Build rows for houses 1 to 4 (index 0 to 3)
                    for i in range(4):
                        row = [
                            str(i + 1),
                            names[i],
                            cigars[i],
                            sports[i],
                            drinks[i]
                        ]
                        solution["solution"]["rows"].append(row)
                    # We assume a unique solution and break out of all loops.
                    print(json.dumps(solution, indent=2))
                    return

if __name__ == '__main__':
    main()