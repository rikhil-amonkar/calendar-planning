#!/usr/bin/env python3
import json
import itertools

def main():
    # Define all possible attribute lists
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]

    solution = None

    # There are 3 houses: indices 0, 1, 2 correspond to Houses 1,2,3 (left to right)
    for perm_names in itertools.permutations(names):
        for perm_cigars in itertools.permutations(cigars):
            for perm_hobbies in itertools.permutations(hobbies):
                for perm_educations in itertools.permutations(educations):
                    for perm_drinks in itertools.permutations(drinks):
                        # Build houses as a list of dictionaries
                        houses = []
                        for i in range(3):
                            house = {
                                "Name": perm_names[i],
                                "Cigar": perm_cigars[i],
                                "Hobby": perm_hobbies[i],
                                "Education": perm_educations[i],
                                "Drink": perm_drinks[i]
                            }
                            houses.append(house)
                            
                        # Check Clue 1: The person partial to Pall Mall is Peter.
                        # That is, the house with cigar "pall mall" must have name "Peter".
                        valid = True
                        for house in houses:
                            if house["Cigar"] == "pall mall" and house["Name"] != "Peter":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Check Clue 2: The person who likes milk is directly left of the person with a high school diploma.
                        found_pair = False
                        for i in range(2):
                            if houses[i]["Drink"] == "milk" and houses[i+1]["Education"] == "high school":
                                found_pair = True
                        if not found_pair:
                            continue
                        
                        # Check Clue 3: Eric is the tea drinker.
                        for house in houses:
                            if house["Name"] == "Eric" and house["Drink"] != "tea":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Check Clue 4: Arnold and the Prince smoker are next to each other.
                        adjacent_pair = False
                        for i in range(2):
                            if (houses[i]["Name"] == "Arnold" and houses[i+1]["Cigar"] == "prince") or \
                               (houses[i]["Cigar"] == "prince" and houses[i+1]["Name"] == "Arnold"):
                                adjacent_pair = True
                        if not adjacent_pair:
                            continue
                        
                        # Check Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
                        idx_gardening = None
                        idx_prince = None
                        for i in range(3):
                            if houses[i]["Hobby"] == "gardening":
                                idx_gardening = i
                            if houses[i]["Cigar"] == "prince":
                                idx_prince = i
                        if idx_gardening is None or idx_prince is None or idx_gardening >= idx_prince:
                            continue
                        
                        # Check Clue 6: The person who likes milk is the person with an associate's degree.
                        for house in houses:
                            if house["Drink"] == "milk" and house["Education"] != "associate":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Check Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
                        bachelor_left = False
                        for i in range(2):
                            if houses[i]["Education"] == "bachelor" and houses[i+1]["Hobby"] == "photography":
                                bachelor_left = True
                        if not bachelor_left:
                            continue
                        
                        # If all constraints passed, we have found the solution.
                        solution = houses
                        break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    if solution is None:
        result = {"solution": {"header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"], "rows": []}}
    else:
        # Format the solution in the required JSON structure.
        rows = []
        # Houses are 1-indexed in output.
        for i, house in enumerate(solution):
            row = [
                str(i+1),
                house["Name"],
                house["Cigar"],
                house["Hobby"],
                house["Education"],
                house["Drink"]
            ]
            rows.append(row)
        result = {"solution": {"header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"], "rows": rows}}
        
    print(json.dumps(result))

if __name__ == '__main__':
    main()