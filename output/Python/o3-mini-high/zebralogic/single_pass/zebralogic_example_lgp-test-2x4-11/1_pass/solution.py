#!/usr/bin/env python3
import itertools
import json

def main():
    houses_count = 2
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]

    solution = None

    # Generate all possible assignments using permutations
    for perm_names in itertools.permutations(names):
        for perm_hobbies in itertools.permutations(hobbies):
            for perm_pets in itertools.permutations(pets):
                for perm_heights in itertools.permutations(heights):
                    houses = []
                    for i in range(houses_count):
                        houses.append({
                            "Name": perm_names[i],
                            "Hobby": perm_hobbies[i],
                            "Pet": perm_pets[i],
                            "Height": perm_heights[i]
                        })

                    # Constraint 1: The person who is very short is the photography enthusiast.
                    valid1 = True
                    for house in houses:
                        if house["Height"] == "very short" and house["Hobby"] != "photography":
                            valid1 = False
                            break
                    if not valid1:
                        continue

                    # Constraint 2: Eric is the person who is very short.
                    valid2 = True
                    for house in houses:
                        if house["Name"] == "Eric" and house["Height"] != "very short":
                            valid2 = False
                            break
                    if not valid2:
                        continue

                    # Constraint 3: The person who has a cat is somewhere to the right of the person who is very short.
                    index_very_short = None
                    index_cat = None
                    for i, house in enumerate(houses):
                        if house["Height"] == "very short":
                            index_very_short = i
                        if house["Pet"] == "cat":
                            index_cat = i
                    if index_very_short is None or index_cat is None or index_cat <= index_very_short:
                        continue

                    solution = houses
                    break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    if solution is not None:
        header = ["House", "Name", "Hobby", "Pet", "Height"]
        rows = []
        for i, house in enumerate(solution):
            row = [str(i+1), house["Name"], house["Hobby"], house["Pet"], house["Height"]]
            rows.append(row)
        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output))

if __name__ == '__main__':
    main()