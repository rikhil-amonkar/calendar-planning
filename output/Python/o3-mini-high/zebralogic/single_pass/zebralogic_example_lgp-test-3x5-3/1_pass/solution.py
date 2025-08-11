#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Eric", "Peter", "Arnold"]
    smoothies = ["cherry", "watermelon", "desert"]
    flowers = ["carnations", "lilies", "daffodils"]
    animals = ["cat", "horse", "bird"]
    hobbies = ["photography", "cooking", "gardening"]

    solution = None
    # Iterate through all possible assignments of attributes to houses
    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for flower_perm in itertools.permutations(flowers):
                for animal_perm in itertools.permutations(animals):
                    for hobby_perm in itertools.permutations(hobbies):
                        valid = True
                        # Check constraints that apply to each house individually
                        for i in range(3):
                            # Clue 8: The photography enthusiast is Eric.
                            if hobby_perm[i] == "photography" and name_perm[i] != "Eric":
                                valid = False
                                break
                            if name_perm[i] == "Eric" and hobby_perm[i] != "photography":
                                valid = False
                                break
                            # Clue 3: The person who loves cooking is the Desert smoothie lover.
                            if hobby_perm[i] == "cooking" and smoothie_perm[i] != "desert":
                                valid = False
                                break
                            if smoothie_perm[i] == "desert" and hobby_perm[i] != "cooking":
                                valid = False
                                break
                            # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
                            if hobby_perm[i] == "gardening" and flower_perm[i] != "carnations":
                                valid = False
                                break
                            if flower_perm[i] == "carnations" and hobby_perm[i] != "gardening":
                                valid = False
                                break
                            # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
                            if flower_perm[i] == "daffodils" and smoothie_perm[i] != "desert":
                                valid = False
                                break
                            if smoothie_perm[i] == "desert" and flower_perm[i] != "daffodils":
                                valid = False
                                break
                            # Clue 2: The bird keeper is the person who likes Cherry smoothies.
                            if animal_perm[i] == "bird" and smoothie_perm[i] != "cherry":
                                valid = False
                                break
                            if smoothie_perm[i] == "cherry" and animal_perm[i] != "bird":
                                valid = False
                                break
                            # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
                            if smoothie_perm[i] == "watermelon" and animal_perm[i] != "horse":
                                valid = False
                                break
                            if animal_perm[i] == "horse" and smoothie_perm[i] != "watermelon":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
                        pos_horse = None
                        pos_photography = None
                        for i in range(3):
                            if animal_perm[i] == "horse":
                                pos_horse = i
                            if hobby_perm[i] == "photography":
                                pos_photography = i
                        if pos_horse is None or pos_photography is None or abs(pos_horse - pos_photography) != 1:
                            continue

                        # Clue 5: The person who loves cooking is directly left of Peter.
                        pos_cooking = None
                        pos_peter = None
                        for i in range(3):
                            if hobby_perm[i] == "cooking":
                                pos_cooking = i
                            if name_perm[i] == "Peter":
                                pos_peter = i
                        if pos_cooking is None or pos_peter is None or pos_cooking != pos_peter - 1:
                            continue

                        # If all constraints are satisfied, record the solution
                        solution = []
                        for i in range(3):
                            # House numbers are maintained as strings "1", "2", "3"
                            solution.append([
                                str(i + 1),
                                name_perm[i],
                                smoothie_perm[i],
                                flower_perm[i],
                                animal_perm[i],
                                hobby_perm[i]
                            ])
                        break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()