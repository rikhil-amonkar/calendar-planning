#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Iterate over all possible orderings of names, mothers, and pets.
    for name_perm in itertools.permutations(names):
        # Constraint 1: Bob is not in the second house.
        if name_perm[1] == "Bob":
            continue

        # Constraint 8: Alice is directly left of Carol.
        if not any(name_perm[i] == "Alice" and name_perm[i+1] == "Carol" for i in range(5)):
            continue

        try:
            idx_arnold = name_perm.index("Arnold")
            idx_eric = name_perm.index("Eric")
            idx_carol = name_perm.index("Carol")
        except ValueError:
            continue

        for mother_perm in itertools.permutations(mothers):
            # Constraint 7: The person who has a cat (Arnold) must have mother's name Janelle.
            if mother_perm[idx_arnold] != "Janelle":
                continue

            # Constraint 9: Carol is the person whose mother's name is Aniya.
            if mother_perm[idx_carol] != "Aniya":
                continue

            # Constraint 11: The person whose mother's name is Kailyn is the one who owns a rabbit (Eric).
            if mother_perm[idx_eric] != "Kailyn":
                continue

            # Constraint 3: The person who has a cat is directly left of the person whose mother's name is Holly.
            # (Arnold has cat; so the house immediately to the right of Arnold must have mother Holly.)
            if idx_arnold == 5 or mother_perm[idx_arnold + 1] != "Holly":
                continue

            for pet_perm in itertools.permutations(pets):
                # Constraint 10 & 5: Arnold must have a cat and Eric must have a rabbit.
                if pet_perm[idx_arnold] != "cat" or pet_perm[idx_eric] != "rabbit":
                    continue

                # Constraint 4: The person with a pet hamster is directly left of the person who owns a rabbit.
                hamster_left_of_rabbit = any(pet_perm[i] == "hamster" and pet_perm[i+1] == "rabbit" for i in range(5))
                if not hamster_left_of_rabbit:
                    continue

                # Constraint 2: There are two houses between the person who has a cat and the person who owns a rabbit.
                if abs(idx_arnold - idx_eric) != 3:
                    continue

                # Constraint 6: There is one house between the person who owns a dog and the person who has a cat.
                try:
                    idx_dog = pet_perm.index("dog")
                except ValueError:
                    continue
                if abs(idx_dog - idx_arnold) != 2:
                    continue

                # Constraint 12: The person with the aquarium of fish is the person whose mother's name is Sarah.
                # For every house where the pet is fish, the corresponding mother must be Sarah.
                valid_fish = True
                for i in range(6):
                    if pet_perm[i] == "fish" and mother_perm[i] != "Sarah":
                        valid_fish = False
                        break
                if not valid_fish:
                    continue

                # All constraints satisfied; build the solution.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "mother", "pet"],
                        "rows": []
                    }
                }
                for i in range(6):
                    house_number = str(i + 1)
                    row = [house_number, name_perm[i], mother_perm[i], pet_perm[i]]
                    solution["solution"]["rows"].append(row)
                print(json.dumps(solution, indent=2))
                return

if __name__ == '__main__':
    main()