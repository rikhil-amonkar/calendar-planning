#!/usr/bin/env python3
import itertools
import json

# Define all attributes.
names_all = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
drinks_all = ["milk", "root beer", "coffee", "tea", "water"]
colors_all = ["blue", "green", "white", "yellow", "red"]
flowers_all = ["daffodils", "roses", "lilies", "tulips", "carnations"]
hobbies_all = ["painting", "cooking", "photography", "gardening", "knitting"]

# A helper generator to yield all permutations with fixed positions.
def perm_fixed(items, fixed):
    n = len(items)
    free_indices = [i for i in range(n) if i not in fixed]
    free_items = [item for item in items if item not in fixed.values()]
    for perm in itertools.permutations(free_items):
        candidate = [None] * n
        for i, val in fixed.items():
            candidate[i] = val
        for idx, pos in enumerate(free_indices):
            candidate[pos] = perm[idx]
        yield candidate

def check_solution(names, drinks, colors, flowers, hobbies):
    # Constraint 1: Alice is not in the fourth house (index 3)
    if names[3] == "Alice":
        return False

    # Constraint 8 & 13: The water drinker must be Peter and water is in the third house (index2)
    if drinks[2] != "water" or names[2] != "Peter":
        return False
    for i in range(5):
        if drinks[i] == "water" and names[i] != "Peter":
            return False
        if names[i] == "Peter" and drinks[i] != "water":
            return False

    # Constraint 2 and 14: Root beer lover is the one who enjoys gardening,
    # and the person who loves carnations is the root beer lover.
    for i in range(5):
        if drinks[i] == "root beer":
            if hobbies[i] != "gardening" or flowers[i] != "carnations":
                return False
        if hobbies[i] == "gardening" and drinks[i] != "root beer":
            return False
        if flowers[i] == "carnations" and drinks[i] != "root beer":
            return False

    # Constraint 3 and 4: The person whose favorite color is green is the coffee drinker
    # and also loves lilies. (Equivalence)
    for i in range(5):
        if colors[i] == "green":
            if drinks[i] != "coffee" or flowers[i] != "lilies":
                return False
        if drinks[i] == "coffee" or flowers[i] == "lilies":
            if colors[i] != "green":
                return False

    # Constraint 10: The person whose favorite color is white loves roses.
    for i in range(5):
        if colors[i] == "white" and flowers[i] != "roses":
            return False
        if flowers[i] == "roses" and colors[i] != "white":
            return False

    # Constraint 5: The person who loves blue is somewhere to the right of 
    # the person who loves a bouquet of daffodils.
    try:
        index_blue = colors.index("blue")
        index_daffodils = flowers.index("daffodils")
    except ValueError:
        return False
    if not (index_blue > index_daffodils):
        return False

    # Constraint 6: The person who loves cooking is the person who loves blue.
    for i in range(5):
        if hobbies[i] == "cooking" and colors[i] != "blue":
            return False
        if colors[i] == "blue" and hobbies[i] != "cooking":
            return False

    # Constraint 7: Eric is directly left of the tea drinker.
    try:
        index_eric = names.index("Eric")
    except ValueError:
        return False
    if index_eric == 4 or drinks[index_eric + 1] != "tea":
        return False

    # Constraint 9: Arnold is the photography enthusiast.
    try:
        index_arnold = names.index("Arnold")
    except ValueError:
        return False
    if hobbies[index_arnold] != "photography":
        return False

    # Constraint 11: There is one house between the person who loves carnations and the one whose favorite color is red.
    try:
        index_carnations = flowers.index("carnations")
        index_red = colors.index("red")
    except ValueError:
        return False
    if abs(index_carnations - index_red) != 2:
        return False

    # Constraint 12: The person who loves cooking is somewhere to the left of the person who paints.
    try:
        index_cooking = hobbies.index("cooking")
        index_painting = hobbies.index("painting")
    except ValueError:
        return False
    if not (index_cooking < index_painting):
        return False

    return True

def main():
    # Fixed positions:
    # For names: House3 (index 2) is Peter.
    names_fixed = {2: "Peter"}
    # For drinks: House3 (index 2) is water.
    drinks_fixed = {2: "water"}
    # For colors: House2 (index 1) is white.
    colors_fixed = {1: "white"}
    # For flowers: House2 (index 1) is roses.
    flowers_fixed = {1: "roses"}
    
    for names in perm_fixed(names_all, names_fixed):
        # Constraint 1: Alice is not in the fourth house (index 3)
        if names[3] == "Alice":
            continue
        # Also, Eric cannot be in last house because he must have a right neighbor (clue 7)
        if names[4] == "Eric":
            continue

        for drinks in perm_fixed(drinks_all, drinks_fixed):
            # (No extra check needed here because water is fixed to house3.)
            for colors in perm_fixed(colors_all, colors_fixed):
                # Constraint 3 & 4 can be partially checked now:
                valid_gc = True
                for i in range(5):
                    if colors[i] == "green":
                        if drinks[i] != "coffee":
                            valid_gc = False
                            break
                    if drinks[i] == "coffee":
                        if colors[i] != "green":
                            valid_gc = False
                            break
                if not valid_gc:
                    continue

                for flowers in perm_fixed(flowers_all, flowers_fixed):
                    valid_fl = True
                    for i in range(5):
                        # Constraint 2 & 14: root beer and carnations
                        if drinks[i] == "root beer" and flowers[i] != "carnations":
                            valid_fl = False
                            break
                        if flowers[i] == "carnations" and drinks[i] != "root beer":
                            valid_fl = False
                            break
                        # Constraint 4: green <-> lilies
                        if colors[i] == "green" and flowers[i] != "lilies":
                            valid_fl = False
                            break
                        if flowers[i] == "lilies" and colors[i] != "green":
                            valid_fl = False
                            break
                        # Constraint 10: white <-> roses
                        if colors[i] == "white" and flowers[i] != "roses":
                            valid_fl = False
                            break
                        if flowers[i] == "roses" and colors[i] != "white":
                            valid_fl = False
                            break
                    if not valid_fl:
                        continue

                    # Constraint 11: One house between carnations and red
                    try:
                        index_carnations = flowers.index("carnations")
                        index_red = colors.index("red")
                    except ValueError:
                        continue
                    if abs(index_carnations - index_red) != 2:
                        continue

                    # Constraint 5: Blue house is to the right of the daffodils bouquet.
                    try:
                        index_blue = colors.index("blue")
                        index_daffodils = flowers.index("daffodils")
                    except ValueError:
                        continue
                    if not (index_blue > index_daffodils):
                        continue

                    for hobbies in itertools.permutations(hobbies_all):
                        # Constraint 6: Cooking and blue are the same house.
                        valid_hobby = True
                        for i in range(5):
                            if hobbies[i] == "cooking" and colors[i] != "blue":
                                valid_hobby = False
                                break
                            if colors[i] == "blue" and hobbies[i] != "cooking":
                                valid_hobby = False
                                break
                        if not valid_hobby:
                            continue

                        # Constraint 7: Eric is directly left of the tea drinker.
                        try:
                            index_eric = names.index("Eric")
                        except ValueError:
                            continue
                        if index_eric == 4 or drinks[index_eric + 1] != "tea":
                            continue

                        # Constraint 9: Arnold is the photography enthusiast.
                        try:
                            index_arnold = names.index("Arnold")
                        except ValueError:
                            continue
                        if hobbies[index_arnold] != "photography":
                            continue

                        # Constraint 12: Cooking is somewhere to the left of painting.
                        try:
                            index_cooking = hobbies.index("cooking")
                            index_painting = hobbies.index("painting")
                        except ValueError:
                            continue
                        if not (index_cooking < index_painting):
                            continue

                        # All constraints have been checked.
                        if check_solution(names, drinks, colors, flowers, hobbies):
                            solution_rows = []
                            for i in range(5):
                                # Houses are numbered 1 to 5 from left to right.
                                solution_rows.append([
                                    str(i+1), 
                                    names[i],
                                    drinks[i],
                                    colors[i],
                                    flowers[i],
                                    hobbies[i]
                                ])
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(result, indent=2))
                            return

if __name__ == '__main__':
    main()