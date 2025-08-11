#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    # Define the attributes for each category.
    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]

    # There are 4 houses, indexed 0 to 3 (house number = index+1).
    # We'll iterate over all possible assignments (permutations) for each attribute
    # and then check if they satisfy all the given clues.
    for perm_names in itertools.permutations(names):
        for perm_smoothies in itertools.permutations(smoothies):
            # Clue 9: The Watermelon smoothie lover is not in the first house.
            if perm_smoothies[0] == "watermelon":
                continue
            for perm_sports in itertools.permutations(sports):
                # Clue 4: The person who loves tennis is in the first house.
                if perm_sports[0] != "tennis":
                    continue
                # Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
                if abs(perm_sports.index("tennis") - perm_sports.index("soccer")) != 1:
                    continue
                for perm_cars in itertools.permutations(cars):
                    for perm_flowers in itertools.permutations(flowers):
                        # Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
                        if perm_cars.index("tesla model 3") != perm_flowers.index("roses"):
                            continue
                        # Clue 2: Peter is the Dragonfruit smoothie lover.
                        if perm_smoothies[perm_names.index("Peter")] != "dragonfruit":
                            continue
                        # Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
                        if perm_cars[perm_smoothies.index("desert")] != "toyota camry":
                            continue
                        # Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
                        if abs(perm_cars.index("toyota camry") - perm_sports.index("basketball")) != 1:
                            continue
                        # Clue 6: Arnold is the person who loves basketball.
                        if perm_sports[perm_names.index("Arnold")] != "basketball":
                            continue
                        # Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
                        if perm_flowers[perm_cars.index("honda civic")] != "daffodils":
                            continue
                        # Clue 8: Eric is the person who loves the rose bouquet.
                        if perm_flowers[perm_names.index("Eric")] != "roses":
                            continue
                        # Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
                        if not (perm_cars.index("honda civic") > perm_smoothies.index("desert")):
                            continue
                        # Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
                        if perm_flowers[perm_sports.index("basketball")] != "lilies":
                            continue

                        # If we reach here, all constraints are satisfied.
                        header = ["House", "Name", "Smoothie", "Sport", "Car", "Flower"]
                        rows = []
                        # Houses are numbered 1 to 4 (left to right corresponds to index 0 to 3)
                        for i in range(4):
                            row = [str(i+1), perm_names[i], perm_smoothies[i], perm_sports[i], perm_cars[i], perm_flowers[i]]
                            rows.append(row)
                        solution = {
                            "solution": {
                                "header": header,
                                "rows": rows
                            }
                        }
                        print(json.dumps(solution, indent=2))
                        sys.exit(0)
                        
if __name__ == "__main__":
    main()