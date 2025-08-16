#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationalities = ["german", "swede", "norwegian", "brit", "dane"]
    
    # The puzzle constraints:
    # House numbers: 1 to 5 (we use indices 0 to 4)
    # Clue 11: The person who keeps horses is in the third house -> index 2 must be "horse".
    # Clue 3: The Dane is the person who keeps horses -> house at index 2 must have nationality "dane".
    # Clue 12: The Norwegian is Alice -> whichever house is "norwegian" must have name "Alice" and vice versa.
    # Clue 6: Eric is the cat lover -> house with name "Eric" must have animal "cat".
    # Clue 7: Bob is the bird keeper -> house with name "Bob" must have animal "bird".
    # Clue 9: The bird keeper drinks Watermelon smoothies -> house with "Bob" gets "watermelon" smoothie.
    # Clue 10: The Desert smoothie lover is the dog owner -> house with smoothie "desert" must have animal "dog" (and vice‐versa).
    # Clue 1: The Swedish person is directly left of the dog owner.
    # Clue 2: There are two houses between the dog owner and the British person.
    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    
    for nat in itertools.permutations(nationalities):
        # Enforce: third house (index 2) is "dane"
        if nat[2] != "dane":
            continue
        
        for name_perm in itertools.permutations(names):
            valid_name_nat = True
            for i in range(5):
                # The Norwegian must be Alice (and vice versa)
                if nat[i] == "norwegian" and name_perm[i] != "Alice":
                    valid_name_nat = False
                    break
                if name_perm[i] == "Alice" and nat[i] != "norwegian":
                    valid_name_nat = False
                    break
            if not valid_name_nat:
                continue
            
            for animal_perm in itertools.permutations(animals):
                # Enforce: third house (index 2) is "horse"
                if animal_perm[2] != "horse":
                    continue
                valid_animals = True
                for i in range(5):
                    # Eric must be the cat lover.
                    if name_perm[i] == "Eric" and animal_perm[i] != "cat":
                        valid_animals = False
                        break
                    # Bob must be the bird keeper.
                    if name_perm[i] == "Bob" and animal_perm[i] != "bird":
                        valid_animals = False
                        break
                if not valid_animals:
                    continue
                
                for smoothie_perm in itertools.permutations(smoothies):
                    valid_smoothie = True
                    # Constraint: The Desert smoothie lover is the dog owner (and vice versa).
                    for i in range(5):
                        if smoothie_perm[i] == "desert" and animal_perm[i] != "dog":
                            valid_smoothie = False
                            break
                        if animal_perm[i] == "dog" and smoothie_perm[i] != "desert":
                            valid_smoothie = False
                            break
                    if not valid_smoothie:
                        continue

                    # Find index of dog owner.
                    try:
                        idx_dog = animal_perm.index("dog")
                    except ValueError:
                        continue
                    # The dog owner must have a left neighbor (because of clue 1) and right neighbor (clue 5)
                    if idx_dog == 0 or idx_dog == 4:
                        continue
                    # Clue 5: Dog owner is directly left of the person who drinks Lime smoothies.
                    if smoothie_perm[idx_dog + 1] != "lime":
                        continue
                    # Clue 1: The Swedish person is directly left of the dog owner.
                    if nat[idx_dog - 1] != "swede":
                        continue
                    # Clue 2: There are two houses between the dog owner and the British person.
                    try:
                        idx_brit = nat.index("brit")
                    except ValueError:
                        continue
                    if abs(idx_dog - idx_brit) != 3:
                        continue
                    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
                    try:
                        idx_peter = name_perm.index("Peter")
                    except ValueError:
                        continue
                    if idx_peter == 0 or smoothie_perm[idx_peter - 1] != "cherry":
                        continue
                    # Clue 9: The bird keeper is the Watermelon smoothie lover.
                    try:
                        idx_bob = name_perm.index("Bob")
                    except ValueError:
                        continue
                    if smoothie_perm[idx_bob] != "watermelon":
                        continue
                    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
                    try:
                        idx_eric = name_perm.index("Eric")
                    except ValueError:
                        continue
                    if idx_bob <= idx_eric:
                        continue
                    
                    # If all constraints are satisfied, output the solution.
                    solution_rows = []
                    for i in range(5):
                        house_number = str(i + 1)
                        row = [house_number, name_perm[i], smoothie_perm[i], animal_perm[i], nat[i]]
                        solution_rows.append(row)
                    
                    output = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(output, indent=2))
                    sys.exit(0)

if __name__ == "__main__":
    main()