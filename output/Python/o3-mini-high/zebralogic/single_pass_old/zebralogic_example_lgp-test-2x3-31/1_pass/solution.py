#!/usr/bin/env python3
import json
from itertools import permutations

def solve_puzzle():
    # Define houses and attributes as given
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    favorite_sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    # Try all possible assignments
    for name_perm in permutations(names):
        for sport_perm in permutations(favorite_sports):
            for hobby_perm in permutations(hobbies):
                valid = True
                for i, house in enumerate(houses):
                    name = name_perm[i]
                    sport = sport_perm[i]
                    hobby = hobby_perm[i]
                    # Clue 2: The photography enthusiast is not in the first house.
                    if house == 1 and hobby == "photography":
                        valid = False
                        break
                    # Clue 3: The person who loves soccer is not in the first house.
                    if house == 1 and sport == "soccer":
                        valid = False
                        break
                    # Clue 1: The person who enjoys gardening is Arnold.
                    if hobby == "gardening" and name != "Arnold":
                        valid = False
                        break
                if valid:
                    # Build the solution in the required format.
                    solution = {
                        "header": ["House", "Name", "favorite sports", "hobby"],
                        "rows": []
                    }
                    for i, house in enumerate(houses):
                        row = [str(house), name_perm[i], sport_perm[i], hobby_perm[i]]
                        solution["rows"].append(row)
                    return solution
    return None

if __name__ == "__main__":
    solution = solve_puzzle()
    output = {"solution": solution}
    print(json.dumps(output, indent=2))