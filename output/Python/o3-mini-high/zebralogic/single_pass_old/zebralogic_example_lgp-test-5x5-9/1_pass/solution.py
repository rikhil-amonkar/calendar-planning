#!/usr/bin/env python3
import itertools
import json

def main():
    # Define attribute lists.
    names_list = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks_list = ["milk", "root beer", "coffee", "tea", "water"]
    colors_list = ["blue", "green", "white", "yellow", "red"]
    flowers_list = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies_list = ["painting", "cooking", "photography", "gardening", "knitting"]

    # Precompute valid permutations that satisfy fixed-position constraints.
    # House numbers: index 0=house 1, index 1=house 2, index 2=house 3, etc.
    valid_names = [perm for perm in itertools.permutations(names_list)
                   if perm[2] == "Peter" and perm[3] != "Alice"]
    valid_drinks = [perm for perm in itertools.permutations(drinks_list)
                    if perm[2] == "water"]
    valid_colors = [perm for perm in itertools.permutations(colors_list)
                    if perm[1] == "white"]
    valid_flowers = [perm for perm in itertools.permutations(flowers_list)
                     if perm[1] == "roses"]
    valid_hobbies = list(itertools.permutations(hobbies_list))
    
    solution = None
    found = False

    # Iterate over all candidate assignments.
    for names_perm in valid_names:
        for drinks_perm in valid_drinks:
            # Clue 7: Eric is directly left of the tea drinker.
            try:
                tea_index = drinks_perm.index("tea")
            except ValueError:
                continue
            # Tea can't be at the first house.
            if tea_index == 0 or names_perm[tea_index - 1] != "Eric":
                continue

            for colors_perm in valid_colors:
                # Clue 3: The person whose favorite color is green is the coffee drinker.
                valid_color = True
                for i in range(5):
                    if colors_perm[i] == "green" and drinks_perm[i] != "coffee":
                        valid_color = False
                        break
                if not valid_color:
                    continue

                for flowers_perm in valid_flowers:
                    # Clue 4: The person whose favorite color is green loves lilies.
                    valid_flowers_flag = True
                    for i in range(5):
                        if colors_perm[i] == "green" and flowers_perm[i] != "lilies":
                            valid_flowers_flag = False
                            break
                    if not valid_flowers_flag:
                        continue

                    # Clue 5: The person who loves blue is somewhere to the right of the person who loves daffodils.
                    try:
                        index_daffodils = flowers_perm.index("daffodils")
                        index_blue = colors_perm.index("blue")
                    except ValueError:
                        continue
                    if index_blue <= index_daffodils:
                        continue

                    # Clue 11: There is one house between the person who loves carnations and the person whose favorite color is red.
                    try:
                        index_carnations = flowers_perm.index("carnations")
                        index_red = colors_perm.index("red")
                    except ValueError:
                        continue
                    if abs(index_carnations - index_red) != 2:
                        continue

                    # Clue 14: The person who loves carnations is the root beer lover.
                    flowers_drink_ok = True
                    for i in range(5):
                        if flowers_perm[i] == "carnations" and drinks_perm[i] != "root beer":
                            flowers_drink_ok = False
                            break
                    if not flowers_drink_ok:
                        continue

                    for hobbies_perm in valid_hobbies:
                        # Clue 2 & 14: The root beer lover enjoys gardening.
                        valid_hobby = True
                        for i in range(5):
                            if drinks_perm[i] == "root beer" and hobbies_perm[i] != "gardening":
                                valid_hobby = False
                                break
                            if hobbies_perm[i] == "gardening" and drinks_perm[i] != "root beer":
                                valid_hobby = False
                                break
                        if not valid_hobby:
                            continue

                        # Clue 6: The person who loves cooking is the person who loves blue.
                        # That is, the house with cooking should be the same as the house with blue.
                        if hobbies_perm.index("cooking") != colors_perm.index("blue"):
                            continue

                        # Clue 9: Arnold is the photography enthusiast.
                        arnold_ok = True
                        for i in range(5):
                            if names_perm[i] == "Arnold" and hobbies_perm[i] != "photography":
                                arnold_ok = False
                                break
                        if not arnold_ok:
                            continue

                        # Clue 12: The person who loves cooking is somewhere to the left of the person who paints.
                        if hobbies_perm.index("cooking") >= hobbies_perm.index("painting"):
                            continue

                        # All constraints satisfied; build the solution.
                        sol = {
                            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                            "rows": []
                        }
                        for i in range(5):
                            sol["rows"].append([
                                str(i+1),
                                names_perm[i],
                                drinks_perm[i],
                                colors_perm[i],
                                flowers_perm[i],
                                hobbies_perm[i]
                            ])
                        solution = sol
                        found = True
                        break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break

    if solution is None:
        solution = {"header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"], "rows": []}
    print(json.dumps({"solution": solution}, indent=2))

if __name__ == "__main__":
    main()