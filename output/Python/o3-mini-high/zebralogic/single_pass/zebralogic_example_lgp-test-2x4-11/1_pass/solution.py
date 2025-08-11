#!/usr/bin/env python3
import itertools
import json

def main():
    # Define attributes
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    pets = ['cat', 'dog']
    heights = ['short', 'very short']
    
    solution = None

    # Iterate over all permutations for each attribute category
    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for pet_perm in itertools.permutations(pets):
                for height_perm in itertools.permutations(heights):
                    houses = []
                    for i in range(2):
                        houses.append({
                            "House": str(i + 1),
                            "Name": name_perm[i],
                            "Hobby": hobby_perm[i],
                            "Pet": pet_perm[i],
                            "Height": height_perm[i]
                        })
                    
                    valid = True
                    
                    # Constraint 1: The person who is very short is the photography enthusiast.
                    for house in houses:
                        if house["Height"] == "very short" and house["Hobby"] != "photography":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Constraint 2: Eric is the person who is very short.
                    for house in houses:
                        if house["Name"] == "Eric" and house["Height"] != "very short":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Constraint 3: The person who has a cat is somewhere to the right of the person who is very short.
                    index_very_short = None
                    index_cat = None
                    for idx, house in enumerate(houses):
                        if house["Height"] == "very short":
                            index_very_short = idx
                        if house["Pet"] == "cat":
                            index_cat = idx
                    if index_very_short is None or index_cat is None or index_cat <= index_very_short:
                        valid = False
                    if not valid:
                        continue

                    solution = houses
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    # Build the output JSON structure
    header = ["House", "Name", "Hobby", "Pet", "Height"]
    rows = []
    if solution:
        for house in solution:
            row = [house[attr] for attr in header]
            rows.append(row)
            
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(output))

if __name__ == '__main__':
    main()