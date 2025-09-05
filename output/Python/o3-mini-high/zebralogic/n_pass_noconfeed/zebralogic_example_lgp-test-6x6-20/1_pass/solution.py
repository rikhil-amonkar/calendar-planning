#!/usr/bin/env python3
import json
from itertools import product
import sys

# Define the six attribute sets.
NAMES = {"Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"}
CIGARS = {"pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"}
MUSIC = {"hip hop", "jazz", "country", "pop", "classical", "rock"}
DRINKS = {"water", "milk", "boba tea", "tea", "root beer", "coffee"}
MOTHERS = {"Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"}
FOODS = {"soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"}

# Global constraint-check function.
def valid(solution):
    n = len(solution)
    # Constraint 1: Carol is directly left of the person who loves grilled cheese.
    for i, h in enumerate(solution):
        if h["Name"] == "Carol":
            # Carol cannot be in house 6.
            if i == 5:
                return False
            # If the right neighbour is assigned, it must have grilled cheese.
            if i + 1 < n and solution[i + 1]["Food"] != "grilled cheese":
                return False
        if h["Food"] == "grilled cheese":
            # Grilled cheese cannot be in house 1.
            if i == 0:
                return False
            if solution[i - 1]["Name"] != "Carol":
                return False

    # Constraint 2: Eric is not in the second house.
    if n > 1:
        if solution[1]["Name"] == "Eric":
            return False

    # Constraint 3: The person whose mother's name is Holly is somewhere to the right of Carol.
    carol_indices = [i for i, h in enumerate(solution) if h["Name"] == "Carol"]
    if carol_indices:
        carol_index = carol_indices[0]
        for i, h in enumerate(solution):
            if h["Mother"] == "Holly" and i <= carol_index:
                return False

    # Constraint 4: The person who loves grilled cheese is somewhere to the right of the person who loves rock music.
    for i, h in enumerate(solution):
        if h["MusicGenre"] == "rock":
            if i == 5:
                return False
            for j, h2 in enumerate(solution):
                if h2["Food"] == "grilled cheese" and j <= i:
                    return False

    # Constraint 5: Eric is directly left of Carol.
    for i, h in enumerate(solution):
        if h["Name"] == "Eric":
            if i == 5:
                return False
            if i + 1 < n and solution[i + 1]["Name"] != "Carol":
                return False
        if h["Name"] == "Carol":
            if i > 0 and solution[i - 1]["Name"] != "Eric":
                return False

    # Constraint 6: The person who loves pop music is not in the third house.
    if n > 2:
        if solution[2]["MusicGenre"] == "pop":
            return False

    # Constraint 7: Eric is the person who loves country music.
    for h in solution:
        if h["Name"] == "Eric":
            if h["MusicGenre"] != "country":
                return False

    # Constraint 8: The person who loves classical music is in the sixth house.
    if n == 6:
        if solution[5]["MusicGenre"] != "classical":
            return False
    else:
        for i, h in enumerate(solution):
            if h["MusicGenre"] == "classical" and i != 5:
                return False

    # Constraint 9: The coffee drinker is Bob.
    for h in solution:
        if h["Name"] == "Bob" and h["Drink"] != "coffee":
            return False

    # Constraint 10: The person who smokes many unique blends is Peter.
    for h in solution:
        if h["Name"] == "Peter" and h["Cigar"] != "blends":
            return False

    # Constraint 11: The person who loves the stew is not in the fifth house.
    if n > 4:
        if solution[4]["Food"] == "stew":
            return False

    # Constraint 12: The root beer lover is directly left of the person whose mother's name is Janelle.
    for i, h in enumerate(solution):
        if h["Drink"] == "root beer":
            if i == 5:
                return False
            if i + 1 < n and solution[i + 1]["Mother"] != "Janelle":
                return False
    for i, h in enumerate(solution):
        if h["Mother"] == "Janelle":
            if i == 0:
                return False
            if solution[i - 1]["Drink"] != "root beer":
                return False

    # Constraint 13: There are two houses between the person whose mother's name is Sarah and the person who smokes Yellow Monster.
    for i, h in enumerate(solution):
        if h["Mother"] == "Sarah":
            for j, h2 in enumerate(solution):
                if h2["Cigar"] == "yellow monster":
                    if abs(i - j) != 3:
                        return False

    # Constraint 14: Eric is the tea drinker.
    for h in solution:
        if h["Name"] == "Eric" and h["Drink"] != "tea":
            return False

    # Constraint 15: The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
    for i, h in enumerate(solution):
        if h["Food"] == "stir fry":
            if i == 5:
                return False
            for j, h2 in enumerate(solution):
                if h2["Cigar"] == "pall mall" and j <= i:
                    return False

    # Constraint 16: The person who loves the soup is Bob.
    for h in solution:
        if h["Name"] == "Bob" and h["Food"] != "soup":
            return False
        if h["Food"] == "soup" and h["Name"] != "Bob":
            return False

    # Constraint 17: The person who loves hip-hop music is directly left of the person whose mother's name is Kailyn.
    for i, h in enumerate(solution):
        if h["MusicGenre"] == "hip hop":
            if i == 5:
                return False
            if i + 1 < n and solution[i + 1]["Mother"] != "Kailyn":
                return False
    for i, h in enumerate(solution):
        if h["Mother"] == "Kailyn":
            if i > 0 and solution[i - 1]["MusicGenre"] != "hip hop":
                return False

    # Constraint 18: Arnold is somewhere to the right of the person whose mother's name is Kailyn.
    for i, h in enumerate(solution):
        if h["Name"] == "Arnold":
            found = False
            for k in range(i):
                if solution[k]["Mother"] == "Kailyn":
                    found = True
                    break
            if not found:
                return False

    # Constraint 19: The one who only drinks water is directly left of the person who smokes Blue Master.
    for i, h in enumerate(solution):
        if h["Drink"] == "water":
            if i == 5:
                return False
            if i + 1 < n and solution[i + 1]["Cigar"] != "blue master":
                return False
    for i, h in enumerate(solution):
        if h["Cigar"] == "blue master":
            if i == 0:
                return False
            if solution[i - 1]["Drink"] != "water":
                return False

    # Constraint 20: The person who loves the spaghetti is somewhere to the left of the person who smokes many unique blends.
    for i, h in enumerate(solution):
        if h["Food"] == "spaghetti":
            for j, h2 in enumerate(solution):
                if h2["Cigar"] == "blends" and i >= j:
                    return False

    # Constraint 21: The person whose mother's name is Sarah is directly left of the person who loves jazz music.
    for i, h in enumerate(solution):
        if h["Mother"] == "Sarah":
            if i == 5:
                return False
            if i + 1 < n and solution[i + 1]["MusicGenre"] != "jazz":
                return False
    for i, h in enumerate(solution):
        if h["MusicGenre"] == "jazz":
            if i == 0:
                return False
            if solution[i - 1]["Mother"] != "Sarah":
                return False

    # Constraint 22: The person who loves hip-hop music is directly left of the root beer lover.
    for i, h in enumerate(solution):
        if h["MusicGenre"] == "hip hop":
            if i == 5:
                return False
            if i + 1 < n and solution[i + 1]["Drink"] != "root beer":
                return False
    for i, h in enumerate(solution):
        if h["Drink"] == "root beer":
            if i == 0:
                return False
            if solution[i - 1]["MusicGenre"] != "hip hop":
                return False

    # Constraint 23: The one who only drinks water is the person who loves the stew.
    for h in solution:
        if h["Drink"] == "water" and h["Food"] != "stew":
            return False
        if h["Food"] == "stew" and h["Drink"] != "water":
            return False

    # Constraint 24: The Dunhill smoker is not in the second house.
    if n > 1:
        if solution[1]["Cigar"] == "dunhill":
            return False

    # Constraint 25: The person who likes milk is the person whose mother's name is Janelle.
    for h in solution:
        if h["Drink"] == "milk" and h["Mother"] != "Janelle":
            return False
        if h["Mother"] == "Janelle" and h["Drink"] != "milk":
            return False

    # Constraint 26: Eric is the person whose mother's name is Aniya.
    for h in solution:
        if h["Name"] == "Eric" and h["Mother"] != "Aniya":
            return False

    return True

# Backtracking search: assign houses 0 through 5 in order.
def backtrack(solution, avail_names, avail_cigars, avail_music, avail_drinks, avail_mothers, avail_foods):
    if len(solution) == 6:
        if valid(solution):
            return solution
        return None
    index = len(solution)
    # Generate candidate tuples from the remaining possibilities.
    for candidate in product(avail_names, avail_cigars, avail_music, avail_drinks, avail_mothers, avail_foods):
        # candidate tuple: (Name, Cigar, MusicGenre, Drink, Mother, Food)
        # Apply immediate local filtering based on house index and fixed clues.
        # House numbering: index 0 -> house1, index 5 -> house6.
        # Constraint: House 6 must have classical music.
        if index == 5 and candidate[2] != "classical":
            continue
        # Constraint: House 2 (index 1) cannot be Eric and cannot have Dunhill.
        if index == 1:
            if candidate[0] == "Eric":
                continue
            if candidate[1] == "dunhill":
                continue
        # If Name is Eric, then music must be country, drink tea, and mother must be Aniya.
        if candidate[0] == "Eric":
            if candidate[2] != "country":
                continue
            if candidate[3] != "tea":
                continue
            if candidate[4] != "Aniya":
                continue
        # Bob: drink coffee and food soup.
        if candidate[0] == "Bob":
            if candidate[3] != "coffee":
                continue
            if candidate[5] != "soup":
                continue
        # Peter: cigar blends.
        if candidate[0] == "Peter":
            if candidate[1] != "blends":
                continue
        # Carol cannot be in house 6.
        if candidate[0] == "Carol" and index == 5:
            continue
        # Grilled cheese cannot be in house 1.
        if candidate[5] == "grilled cheese" and index == 0:
            continue
        # Stir fry cannot be in house 6.
        if candidate[5] == "stir fry" and index == 5:
            continue
        # Pop is not allowed in house 3 (index 2).
        if index == 2 and candidate[2] == "pop":
            continue
        # Drink and food must coincide: water <-> stew.
        if candidate[3] == "water" and candidate[5] != "stew":
            continue
        if candidate[5] == "stew" and candidate[3] != "water":
            continue
        # Milk and Janelle pair.
        if candidate[3] == "milk" and candidate[4] != "Janelle":
            continue
        if candidate[4] == "Janelle" and candidate[3] != "milk":
            continue
        # Additional local neighbor constraints using the previously assigned house.
        if solution:
            prev = solution[-1]
            # If the previous house is Carol, then by Constraint 1, current must have grilled cheese.
            if prev["Name"] == "Carol":
                if candidate[5] != "grilled cheese":
                    continue
            # If previous house is Eric, then by Constraint 5, current must be Carol.
            if prev["Name"] == "Eric":
                if candidate[0] != "Carol":
                    continue
            # Constraint 12: if previous house drank root beer, current mother's must be Janelle.
            if prev["Drink"] == "root beer":
                if candidate[4] != "Janelle":
                    continue
            # Constraint 17 & 22: if previous house's music is hip hop, current must have mother Kailyn and drink root beer.
            if prev["MusicGenre"] == "hip hop":
                if candidate[4] != "Kailyn" or candidate[3] != "root beer":
                    continue
            # Constraint 19: if previous house drank water, current cigar must be Blue Master.
            if prev["Drink"] == "water":
                if candidate[1] != "blue master":
                    continue
            # Constraint 21: if previous house's mother is Sarah, current music must be jazz.
            if prev["Mother"] == "Sarah":
                if candidate[2] != "jazz":
                    continue

        # Build candidate house dictionary.
        house = {
            "Name": candidate[0],
            "Cigar": candidate[1],
            "MusicGenre": candidate[2],
            "Drink": candidate[3],
            "Mother": candidate[4],
            "Food": candidate[5]
        }
        new_solution = solution + [house]
        if not valid(new_solution):
            continue
        # Update available sets.
        new_avail_names = avail_names - {candidate[0]}
        new_avail_cigars = avail_cigars - {candidate[1]}
        new_avail_music = avail_music - {candidate[2]}
        new_avail_drinks = avail_drinks - {candidate[3]}
        new_avail_mothers = avail_mothers - {candidate[4]}
        new_avail_foods = avail_foods - {candidate[5]}
        sol = backtrack(new_solution, new_avail_names, new_avail_cigars, new_avail_music, new_avail_drinks, new_avail_mothers, new_avail_foods)
        if sol is not None:
            return sol
    return None

def solve_puzzle():
    solution = backtrack([], NAMES, CIGARS, MUSIC, DRINKS, MOTHERS, FOODS)
    return solution

def main():
    sol = solve_puzzle()
    if sol is None:
        sys.exit("No solution found!")
    # Format the solution per house order.
    output = {
        "solution": {
            "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
            "rows": []
        }
    }
    for idx, house in enumerate(sol):
        row = [
            str(idx + 1),
            house["Name"],
            house["Cigar"],
            house["MusicGenre"],
            house["Drink"],
            house["Mother"],
            house["Food"]
        ]
        output["solution"]["rows"].append(row)
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()