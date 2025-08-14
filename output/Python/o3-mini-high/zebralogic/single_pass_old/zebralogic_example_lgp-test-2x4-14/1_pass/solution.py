#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the attributes from the puzzle
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]

    num_houses = 2
    solution = None

    # Iterate over all permutations of the attributes.
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            for smoothie_perm in itertools.permutations(smoothies):
                for pet_perm in itertools.permutations(pets):
                    # Build assignment for each house as a dict.
                    houses = []
                    for i in range(num_houses):
                        houses.append({
                            "House": str(i + 1),
                            "Name": name_perm[i],
                            "House Style": style_perm[i],
                            "Smoothie": smoothie_perm[i],
                            "Pet": pet_perm[i]
                        })
                    
                    valid = True
                    # Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
                    # This implies that for each house, having "cherry" as Smoothie is equivalent to having "dog" as Pet.
                    for house in houses:
                        if (house["Smoothie"] == "cherry") != (house["Pet"] == "dog"):
                            valid = False
                            break

                    if not valid:
                        continue

                    # Clue 2: The person residing in a Victorian house is the person who owns a dog.
                    # So a house is victorian <=> its pet is a dog.
                    for house in houses:
                        if (house["House Style"] == "victorian") != (house["Pet"] == "dog"):
                            valid = False
                            break

                    if not valid:
                        continue

                    # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
                    index_victorian = None
                    index_eric = None
                    for idx, house in enumerate(houses):
                        if house["House Style"] == "victorian":
                            index_victorian = idx
                        if house["Name"] == "Eric":
                            index_eric = idx
                    if index_victorian is None or index_eric is None or not (index_victorian < index_eric):
                        continue

                    # If all clues are satisfied, capture the solution.
                    solution = houses
                    break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    # Prepare the final JSON output according to the required structure.
    if solution:
        output = {
            "solution": {
                "header": ["House", "Name", "House Style", "Smoothie", "Pet"],
                "rows": [
                    [house["House"], house["Name"], house["House Style"], house["Smoothie"], house["Pet"]]
                    for house in solution
                ]
            }
        }
    else:
        output = {"solution": {"header": [], "rows": []}}

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()