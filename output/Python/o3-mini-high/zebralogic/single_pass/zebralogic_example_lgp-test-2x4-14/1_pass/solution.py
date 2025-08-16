#!/usr/bin/env python3
import json
import itertools

def main():
    # Define attributes for the houses
    house_numbers = ["1", "2"]
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]

    # We'll use permutations to assign attributes to houses (house 1, house 2)
    solutions = []
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            for smoothie_perm in itertools.permutations(smoothies):
                for pet_perm in itertools.permutations(pets):
                    # Construct a candidate assignment for the two houses
                    houses = []
                    for i in range(2):
                        house = {
                            "House": house_numbers[i],
                            "Name": name_perm[i],
                            "HouseStyle": style_perm[i],
                            "Smoothie": smoothie_perm[i],
                            "Pet": pet_perm[i]
                        }
                        houses.append(house)
                    
                    valid = True

                    # Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
                    for h in houses:
                        if h["Smoothie"] == "cherry" and h["Pet"] != "dog":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 2: The person residing in a Victorian house is the person who owns a dog.
                    for h in houses:
                        if h["HouseStyle"] == "victorian" and h["Pet"] != "dog":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
                    index_victorian = None
                    index_eric = None
                    for i, h in enumerate(houses):
                        if h["HouseStyle"] == "victorian":
                            index_victorian = i
                        if h["Name"] == "Eric":
                            index_eric = i
                    if index_victorian is None or index_eric is None or index_victorian >= index_eric:
                        continue

                    # If all clues are satisfied, this is a valid solution.
                    solutions.append(houses)
    
    # Assuming one unique solution, take the first found solution.
    if solutions:
        final_solution = solutions[0]
    else:
        final_solution = []

    # Prepare the output in the exact required JSON structure.
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": []
        }
    }
    
    # Ensure rows are ordered by house number (already in order from our assignment)
    for house in final_solution:
        output["solution"]["rows"].append([
            house["House"],
            house["Name"],
            house["HouseStyle"],
            house["Smoothie"],
            house["Pet"]
        ])
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()