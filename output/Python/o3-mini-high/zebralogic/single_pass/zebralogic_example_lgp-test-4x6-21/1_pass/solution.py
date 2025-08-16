#!/usr/bin/env python3
import itertools
import json
import sys

# Define all domains.
names = ["Peter", "Arnold", "Alice", "Eric"]
flowers = ["roses", "daffodils", "carnations", "lilies"]
hobbies = ["photography", "painting", "cooking", "gardening"]
pets = ["dog", "fish", "bird", "cat"]
colors = ["red", "yellow", "green", "white"]
styles = ["craftsman", "colonial", "ranch", "victorian"]

# We use 0-index for houses: house 0 = House "1", house 1 = House "2", etc.

for nperm in itertools.permutations(names):
    # Constraint 1 & 6: The person in a Craftsman-style house is Arnold and that house is the second house.
    # Thus, we force House2 (index 1) to be "Arnold"
    if nperm[1] != "Arnold":
        continue

    for sperm in itertools.permutations(styles):
        # Constraint 6: Craftsman-style must be in the second house.
        if sperm[1] != "craftsman":
            continue

        # Constraint 7: Eric is the person residing in a Victorian house.
        victorian_index = sperm.index("victorian")
        if nperm[victorian_index] != "Eric":
            continue

        # Identify colonial house index (for later constraints).
        colonial_index = sperm.index("colonial")
        
        for cperm in itertools.permutations(colors):
            # Constraint 13: Colonial house must have favorite color red.
            if cperm[colonial_index] != "red":
                continue

            for fperm in itertools.permutations(flowers):
                # Constraint 5: The person who loves the rose bouquet is the person whose favorite color is red.
                # This forces that whichever house has "roses" must have color "red" and vice versa.
                valid_flowers = True
                for i in range(4):
                    # If the house is colonial then it must have roses (by clues 5 and 13).
                    if i == colonial_index and fperm[i] != "roses":
                        valid_flowers = False
                        break
                    # Enforce rose-red link for every house.
                    if fperm[i] == "roses" and cperm[i] != "red":
                        valid_flowers = False
                        break
                    if cperm[i] == "red" and fperm[i] != "roses":
                        valid_flowers = False
                        break
                    # Constraint 12: Daffodils go with yellow.
                    if cperm[i] == "yellow" and fperm[i] != "daffodils":
                        valid_flowers = False
                        break
                    if fperm[i] == "daffodils" and cperm[i] != "yellow":
                        valid_flowers = False
                        break
                    # Constraint 10: White goes with carnations.
                    if cperm[i] == "white" and fperm[i] != "carnations":
                        valid_flowers = False
                        break
                    if fperm[i] == "carnations" and cperm[i] != "white":
                        valid_flowers = False
                        break
                    # Constraint 4: Daffodils are not in the fourth house (index 3).
                    if fperm[i] == "daffodils" and i == 3:
                        valid_flowers = False
                        break
                if not valid_flowers:
                    continue

                for hperm in itertools.permutations(hobbies):
                    # Constraint 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
                    try:
                        red_index = cperm.index("red")
                        cooking_index = hperm.index("cooking")
                        if cooking_index <= red_index:
                            continue
                    except ValueError:
                        continue

                    # Constraint 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
                    try:
                        white_index = cperm.index("white")
                        gardening_index = hperm.index("gardening")
                        if gardening_index >= white_index:
                            continue
                    except ValueError:
                        continue

                    for pperm in itertools.permutations(pets):
                        valid = True
                        # Constraint 3: The photography enthusiast is the person who owns a dog.
                        for i in range(4):
                            if hperm[i] == "photography" and pperm[i] != "dog":
                                valid = False
                                break
                            if pperm[i] == "dog" and hperm[i] != "photography":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 8: The person with an aquarium of fish is the person who loves white.
                        for i in range(4):
                            if pperm[i] == "fish" and cperm[i] != "white":
                                valid = False
                                break
                            if cperm[i] == "white" and pperm[i] != "fish":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 14: The person who has a cat is Eric.
                        for i in range(4):
                            if pperm[i] == "cat" and nperm[i] != "Eric":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 2: The person who loves the rose bouquet is somewhere to the right of Peter.
                        try:
                            roses_index = fperm.index("roses")
                            peter_index = nperm.index("Peter")
                            if roses_index <= peter_index:
                                continue
                        except ValueError:
                            continue

                        # Constraint 9 (redundant check already done) and others have been taken care of.
                        # If we reached here, all constraints are satisfied.
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                                "rows": [
                                    [str(i+1), nperm[i], fperm[i], hperm[i], pperm[i], cperm[i], sperm[i]]
                                    for i in range(4)
                                ]
                            }
                        }
                        print(json.dumps(solution))
                        sys.exit(0)

# If no solution is found, exit.
sys.exit("No solution found.")