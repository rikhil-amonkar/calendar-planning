#!/usr/bin/env python3
import itertools
import json

def main():
    names_list = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks_list = ["milk", "root beer", "coffee", "tea", "water"]
    colors_list = ["blue", "green", "white", "yellow", "red"]
    flowers_list = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies_list = ["painting", "cooking", "photography", "gardening", "knitting"]

    solution = None

    # Iterate over permutations for names.
    for names_perm in itertools.permutations(names_list):
        # House 3 (index 2) must be Peter.
        if names_perm[2] != "Peter":
            continue
        # Alice is not in the fourth house (index 3).
        if names_perm[3] == "Alice":
            continue

        # Iterate over drinks permutations.
        for drinks_perm in itertools.permutations(drinks_list):
            # House 3 must drink water.
            if drinks_perm[2] != "water":
                continue
            # "The water drinker is Peter" is now implicitly enforced: house3 is Peter & water.
            # "Eric is directly left of the tea drinker" (i.e. house immediately right of Eric must have tea)
            try:
                index_eric = names_perm.index("Eric")
            except ValueError:
                continue
            # Eric cannot be in the last house.
            if index_eric == 4:
                continue
            if drinks_perm[index_eric + 1] != "tea":
                continue

            # Iterate over colors permutations.
            for colors_perm in itertools.permutations(colors_list):
                # House 2 must be white.
                if colors_perm[1] != "white":
                    continue
                # For any house that is green, the drink must be coffee.
                valid_green = True
                for i in range(5):
                    if colors_perm[i] == "green" and drinks_perm[i] != "coffee":
                        valid_green = False
                        break
                if not valid_green:
                    continue

                # Iterate over flowers permutations.
                for flowers_perm in itertools.permutations(flowers_list):
                    # For any house that is green, the flower must be lilies.
                    valid_green_flowers = True
                    for i in range(5):
                        if colors_perm[i] == "green" and flowers_perm[i] != "lilies":
                            valid_green_flowers = False
                            break
                    if not valid_green_flowers:
                        continue

                    # For any house where the flower is carnations, the drink must be root beer.
                    valid_carnations = True
                    for i in range(5):
                        if flowers_perm[i] == "carnations" and drinks_perm[i] != "root beer":
                            valid_carnations = False
                            break
                    if not valid_carnations:
                        continue

                    # The person who loves blue must be somewhere to the right of the person who loves daffodils.
                    try:
                        index_blue = colors_perm.index("blue")
                        index_daff = flowers_perm.index("daffodils")
                    except ValueError:
                        continue
                    if not (index_blue > index_daff):
                        continue

                    # There is one house between the person who loves carnations and the person whose favorite color is red.
                    try:
                        index_carn = flowers_perm.index("carnations")
                        index_red = colors_perm.index("red")
                    except ValueError:
                        continue
                    if abs(index_carn - index_red) != 2:
                        continue

                    # Iterate over hobbies permutations.
                    for hobbies_perm in itertools.permutations(hobbies_list):
                        # If a house is blue then its hobby must be cooking.
                        valid_blue_hobby = True
                        for i in range(5):
                            if colors_perm[i] == "blue" and hobbies_perm[i] != "cooking":
                                valid_blue_hobby = False
                                break
                        if not valid_blue_hobby:
                            continue

                        # The root beer lover (and hence the one who loves carnations) must enjoy gardening.
                        valid_rootbeer = True
                        for i in range(5):
                            if drinks_perm[i] == "root beer" and hobbies_perm[i] != "gardening":
                                valid_rootbeer = False
                                break
                        if not valid_rootbeer:
                            continue

                        valid_carnations_hobby = True
                        for i in range(5):
                            if flowers_perm[i] == "carnations" and hobbies_perm[i] != "gardening":
                                valid_carnations_hobby = False
                                break
                        if not valid_carnations_hobby:
                            continue

                        # Arnold is the photography enthusiast.
                        valid_arnold = True
                        for i in range(5):
                            if names_perm[i] == "Arnold" and hobbies_perm[i] != "photography":
                                valid_arnold = False
                                break
                        if not valid_arnold:
                            continue

                        # The person who loves cooking is somewhere to the left of the person who paints.
                        try:
                            index_cooking = hobbies_perm.index("cooking")
                            index_painting = hobbies_perm.index("painting")
                        except ValueError:
                            continue
                        if not (index_cooking < index_painting):
                            continue

                        # All constraints satisfied; record the solution.
                        sol = []
                        for i in range(5):
                            # House numbers are 1-indexed.
                            sol.append([str(i+1), names_perm[i], drinks_perm[i], colors_perm[i], flowers_perm[i], hobbies_perm[i]])
                        solution = sol
                        break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()