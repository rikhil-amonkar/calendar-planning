#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the houses and attributes
    houses = [1, 2]

    names = ["Eric", "Arnold"]
    favorite_sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    # List to collect valid assignments for each house as rows.
    valid_solutions = []

    # Iterate over all possible assignments (permutations) for names, sports, and hobbies
    for perm_names in itertools.permutations(names):
        for perm_sports in itertools.permutations(favorite_sports):
            for perm_hobbies in itertools.permutations(hobbies):
                valid = True
                # Check constraints for each house
                for idx, house in enumerate(houses):
                    current_name = perm_names[idx]
                    current_sport = perm_sports[idx]
                    current_hobby = perm_hobbies[idx]
                    
                    # Constraint 1: The person who enjoys gardening is Arnold.
                    if current_hobby == "gardening" and current_name != "Arnold":
                        valid = False
                        break
                    # Constraint 2: The photography enthusiast is not in the first house.
                    if house == 1 and current_hobby == "photography":
                        valid = False
                        break
                    # Constraint 3: The person who loves soccer is not in the first house.
                    if house == 1 and current_sport == "soccer":
                        valid = False
                        break
                if valid:
                    # Build the assignment rows: each row is [House, Name, FavoriteSport, Hobby]
                    solution_rows = []
                    for idx, house in enumerate(houses):
                        solution_rows.append([str(house), perm_names[idx], perm_sports[idx], perm_hobbies[idx]])
                    valid_solutions.append(solution_rows)
                    
    # Assuming there is only one valid solution given the puzzle constraints.
    solution = valid_solutions[0] if valid_solutions else []

    result = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": solution
        }
    }

    print(json.dumps(result))

if __name__ == '__main__':
    main()