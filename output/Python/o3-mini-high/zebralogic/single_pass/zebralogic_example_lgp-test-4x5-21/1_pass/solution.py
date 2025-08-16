#!/usr/bin/env python3
import itertools
import json

def satisfies_constraints(names, smoothies, sports, cars, flowers):
    # Clue 4: The person who loves tennis is in the first house.
    if sports[0] != "tennis":
        return False
    # Clue 9: The Watermelon smoothie lover is not in the first house.
    if smoothies[0] == "watermelon":
        return False
    # Clue 2: Peter is the Dragonfruit smoothie lover.
    try:
        index_peter = names.index("Peter")
    except ValueError:
        return False
    if smoothies[index_peter] != "dragonfruit":
        return False
    # Clue 8: Eric is the person who loves the rose bouquet.
    try:
        index_eric = names.index("Eric")
    except ValueError:
        return False
    if flowers[index_eric] != "roses":
        return False
    # Clue 6: Arnold is the person who loves basketball.
    try:
        index_arnold = names.index("Arnold")
    except ValueError:
        return False
    if sports[index_arnold] != "basketball":
        return False
    # Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
    for i in range(4):
        if cars[i] == "tesla model 3" and flowers[i] != "roses":
            return False
        if flowers[i] == "roses" and cars[i] != "tesla model 3":
            return False
    # Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
    for i in range(4):
        if smoothies[i] == "desert" and cars[i] != "toyota camry":
            return False
        if cars[i] == "toyota camry" and smoothies[i] != "desert":
            return False
    # Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
    for i in range(4):
        if cars[i] == "honda civic" and flowers[i] != "daffodils":
            return False
        if flowers[i] == "daffodils" and cars[i] != "honda civic":
            return False
    # Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
    for i in range(4):
        if sports[i] == "basketball" and flowers[i] != "lilies":
            return False
        if flowers[i] == "lilies" and sports[i] != "basketball":
            return False
    # Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
    try:
        index_toyota = cars.index("toyota camry")
        index_basketball = sports.index("basketball")
    except ValueError:
        return False
    if abs(index_toyota - index_basketball) != 1:
        return False
    # Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
    try:
        index_tennis = sports.index("tennis")
        index_soccer = sports.index("soccer")
    except ValueError:
        return False
    if abs(index_tennis - index_soccer) != 1:
        return False
    # Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
    try:
        desert_index = smoothies.index("desert")
        honda_index = cars.index("honda civic")
    except ValueError:
        return False
    if honda_index <= desert_index:
        return False

    return True

def main():
    names_list = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies_list = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports_list = ["soccer", "tennis", "basketball", "swimming"]
    cars_list = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers_list = ["daffodils", "roses", "lilies", "carnations"]

    solution = None

    for names_perm in itertools.permutations(names_list):
        for smoothies_perm in itertools.permutations(smoothies_list):
            # Clue 9: first house cannot have watermelon.
            if smoothies_perm[0] == "watermelon":
                continue
            # Clue 2: Peter is the Dragonfruit smoothie lover.
            if smoothies_perm[names_perm.index("Peter")] != "dragonfruit":
                continue
            for sports_perm in itertools.permutations(sports_list):
                # Clue 4: First house must be tennis.
                if sports_perm[0] != "tennis":
                    continue
                # Clue 12: Tennis and Soccer are adjacent.
                if abs(sports_perm.index("tennis") - sports_perm.index("soccer")) != 1:
                    continue
                # Clue 6: Arnold is the person who loves basketball.
                if sports_perm[names_perm.index("Arnold")] != "basketball":
                    continue
                for cars_perm in itertools.permutations(cars_list):
                    # Clue 3: Desert smoothie <-> Toyota Camry.
                    valid = True
                    for i in range(4):
                        if smoothies_perm[i] == "desert" and cars_perm[i] != "toyota camry":
                            valid = False
                            break
                        if cars_perm[i] == "toyota camry" and smoothies_perm[i] != "desert":
                            valid = False
                            break
                    if not valid:
                        continue
                    # Clue 10: Honda Civic must be to the right of the Desert smoothie lover.
                    if cars_perm.index("honda civic") <= smoothies_perm.index("desert"):
                        continue
                    # Clue 5: Toyota Camry and basketball are adjacent.
                    if abs(cars_perm.index("toyota camry") - sports_perm.index("basketball")) != 1:
                        continue
                    for flowers_perm in itertools.permutations(flowers_list):
                        # Clue 8: Eric loves the rose bouquet.
                        if flowers_perm[names_perm.index("Eric")] != "roses":
                            continue
                        # Clue 1: Tesla Model 3 <-> roses.
                        valid = True
                        for i in range(4):
                            if cars_perm[i] == "tesla model 3" and flowers_perm[i] != "roses":
                                valid = False
                                break
                            if flowers_perm[i] == "roses" and cars_perm[i] != "tesla model 3":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 7: Honda Civic <-> daffodils.
                        valid = True
                        for i in range(4):
                            if cars_perm[i] == "honda civic" and flowers_perm[i] != "daffodils":
                                valid = False
                                break
                            if flowers_perm[i] == "daffodils" and cars_perm[i] != "honda civic":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 11: Basketball <-> Lilies.
                        valid = True
                        for i in range(4):
                            if sports_perm[i] == "basketball" and flowers_perm[i] != "lilies":
                                valid = False
                                break
                            if flowers_perm[i] == "lilies" and sports_perm[i] != "basketball":
                                valid = False
                                break
                        if not valid:
                            continue

                        if satisfies_constraints(names_perm, smoothies_perm, sports_perm, cars_perm, flowers_perm):
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                                    "rows": [
                                        [str(i+1), names_perm[i], smoothies_perm[i], sports_perm[i], cars_perm[i], flowers_perm[i]]
                                        for i in range(4)
                                    ]
                                }
                            }
                            print(json.dumps(solution))
                            return

if __name__ == "__main__":
    main()