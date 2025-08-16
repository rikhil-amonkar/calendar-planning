#!/usr/bin/env python3
import itertools
import json

def main():
    houses = [1, 2, 3, 4, 5]  # House numbers 1 to 5 (index 0 corresponds to House "1")
    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]

    # We'll generate all permutations for names, flowers, and animals,
    # then filter them by the puzzle constraints.
    for perm_names in itertools.permutations(names):
        # Constraint 1: Alice is in the second house (index 1)
        if perm_names[1] != "Alice":
            continue
        # Constraint 8 & 5: Alice is directly left of the person who keeps horses AND the horse keeper is Eric.
        # That forces the person immediately right of Alice (house index 2) to be Eric.
        if perm_names[2] != "Eric":
            continue

        for perm_flowers in itertools.permutations(flowers):
            # Constraint 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
            # Locate "carnations" and check that the next house (if exists) has "tulips".
            try:
                index_carnations = perm_flowers.index("carnations")
            except ValueError:
                continue
            if index_carnations == 4 or perm_flowers[index_carnations + 1] != "tulips":
                continue

            for perm_animals in itertools.permutations(animals):
                # Constraint 10: The cat lover is not in the first house.
                if perm_animals[0] == "cat":
                    continue
                # Constraint 8: Alice is directly left of the person who keeps horses.
                index_alice = perm_names.index("Alice")
                if index_alice == 4 or perm_animals[index_alice + 1] != "horse":
                    continue
                # Constraint 5: The person who keeps horses is Eric.
                index_horse = perm_animals.index("horse")
                if perm_names[index_horse] != "Eric":
                    continue

                # Constraint: In house 3 (index 2) must be the person with horses (because Alice in house2 is directly left of horse owner).
                if perm_animals[2] != "horse":
                    continue

                valid = True

                # Constraint 2: The person who loves the bouquet of lilies is the bird keeper.
                for i in range(5):
                    if perm_flowers[i] == "lilies" and perm_animals[i] != "bird":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 4: The fish enthusiast is the person who loves a bouquet of daffodils.
                for i in range(5):
                    if perm_animals[i] == "fish" and perm_flowers[i] != "daffodils":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 7: The fish enthusiast is directly left of Bob.
                if "fish" in perm_animals:
                    index_fish = perm_animals.index("fish")
                    if index_fish == 4 or perm_names[index_fish + 1] != "Bob":
                        valid = False
                if not valid:
                    continue

                # Constraint 6: There are two houses between the dog owner and Bob.
                if "dog" in perm_animals and "Bob" in perm_names:
                    index_dog = perm_animals.index("dog")
                    index_bob = perm_names.index("Bob")
                    if abs(index_dog - index_bob) != 3:
                        valid = False
                if not valid:
                    continue

                # Constraint 3: Peter is somewhere to the right of the person who loves the vase of tulips.
                index_tulips = perm_flowers.index("tulips")
                index_peter = perm_names.index("Peter")
                if index_peter <= index_tulips:
                    continue

                # All constraints satisfied; construct the solution.
                solution_rows = []
                for i in range(5):
                    # House numbers must be strings.
                    solution_rows.append([str(i + 1), perm_names[i], perm_flowers[i], perm_animals[i]])
                result = {
                    "solution": {
                        "header": ["House", "Name", "Flower", "Animal"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(result))
                return

if __name__ == "__main__":
    main()