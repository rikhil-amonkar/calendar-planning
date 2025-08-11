#!/usr/bin/env python3
import itertools
import json

def main():
    houses_positions = [1, 2, 3, 4]
    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthday_months = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    solutions = []
    for perm_names in itertools.permutations(names):
        for perm_hobbies in itertools.permutations(hobbies):
            for perm_months in itertools.permutations(birthday_months):
                for perm_educations in itertools.permutations(educations):
                    for perm_smoothies in itertools.permutations(smoothies):
                        # Build houses: index 0->house 1, etc.
                        houses_assigned = []
                        for i in range(4):
                            houses_assigned.append({
                                "House": str(i+1),
                                "Name": perm_names[i],
                                "Hobby": perm_hobbies[i],
                                "Birthday Month": perm_months[i],
                                "Education": perm_educations[i],
                                "Smoothie": perm_smoothies[i]
                            })
                        
                        valid = True
                        # Clue 4: The person with a high school diploma is in the third house.
                        if houses_assigned[2]["Education"] != "high school":
                            continue
                        # Clue 5: The Watermelon smoothie lover is not in the third house.
                        if houses_assigned[2]["Smoothie"] == "watermelon":
                            continue
                        # Clue 6: The person with an associate's degree is Arnold.
                        for house in houses_assigned:
                            if house["Education"] == "associate" and house["Name"] != "Arnold":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 2: Eric is the person with a bachelor's degree.
                        for house in houses_assigned:
                            if house["Name"] == "Eric" and house["Education"] != "bachelor":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
                        for house in houses_assigned:
                            if house["Smoothie"] == "desert" and house["Birthday Month"] != "jan":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
                        for house in houses_assigned:
                            if house["Birthday Month"] == "jan" and house["Education"] != "bachelor":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 7: The person with a master's degree is the person who paints as a hobby.
                        for house in houses_assigned:
                            if house["Education"] == "master" and house["Hobby"] != "painting":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
                        for house in houses_assigned:
                            if house["Hobby"] == "painting" and house["Birthday Month"] != "feb":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 9: The person with a high school diploma is the person whose birthday is in September.
                        for house in houses_assigned:
                            if house["Education"] == "high school" and house["Birthday Month"] != "sept":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 10: The person who loves cooking is Alice.
                        for house in houses_assigned:
                            if house["Hobby"] == "cooking" and house["Name"] != "Alice":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
                        idx_april = None
                        idx_gardening = None
                        for i, house in enumerate(houses_assigned):
                            if house["Birthday Month"] == "april":
                                idx_april = i
                            if house["Hobby"] == "gardening":
                                idx_gardening = i
                        if idx_april is None or idx_gardening is None or abs(idx_april - idx_gardening) != 1:
                            continue
                        # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
                        idx_dragonfruit = None
                        idx_sept = None
                        for i, house in enumerate(houses_assigned):
                            if house["Smoothie"] == "dragonfruit":
                                idx_dragonfruit = i
                            if house["Birthday Month"] == "sept":
                                idx_sept = i
                        if idx_dragonfruit is None or idx_sept is None or abs(idx_dragonfruit - idx_sept) != 2:
                            continue
                        
                        solutions.append(houses_assigned)
    
    if solutions:
        sol = solutions[0]
        header = ["House", "Name", "Hobby", "Birthday Month", "Education", "Smoothie"]
        rows = []
        for house in sol:
            rows.append([house[col] for col in header])
        output = {"solution": {"header": header, "rows": rows}}
    else:
        output = {"solution": None}
    print(json.dumps(output))

if __name__ == "__main__":
    main()