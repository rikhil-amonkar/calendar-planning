#!/usr/bin/env python3
import itertools
import json

def main():
    names_list = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers_list = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets_list = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Iterate over possible assignments for names (houses 1 to 6, index 0-5)
    for names_perm in itertools.permutations(names_list):
        # Constraint 1: Bob is not in the second house (index 1).
        if names_perm[1] == "Bob":
            continue
        # Constraint 8: Alice is directly left of Carol.
        try:
            idx_alice = names_perm.index("Alice")
            idx_carol = names_perm.index("Carol")
        except ValueError:
            continue
        if idx_alice != idx_carol - 1:
            continue
        # Constraint 5/4: Eric (who owns rabbit) must have a house with a left neighbor for hamster.
        try:
            idx_eric = names_perm.index("Eric")
        except ValueError:
            continue
        if idx_eric == 0:
            continue
        # Constraint 10/3: Arnold (who has cat) must not be in the last house
        try:
            idx_arnold = names_perm.index("Arnold")
        except ValueError:
            continue
        if idx_arnold == 5:
            continue
        # Constraint 2: There are two houses between cat (Arnold) and rabbit (Eric)
        if abs(idx_arnold - idx_eric) != 3:
            continue

        # Iterate over possible assignments for mothers.
        for mothers_perm in itertools.permutations(mothers_list):
            # Constraint 7: The person who has a cat (Arnold) has mother Janelle.
            if mothers_perm[idx_arnold] != "Janelle":
                continue
            # Constraint 11: The person who owns a rabbit (Eric) has mother Kailyn.
            if mothers_perm[idx_eric] != "Kailyn":
                continue
            # Constraint 9: Carol's mother is Aniya.
            if mothers_perm[idx_carol] != "Aniya":
                continue
            # Constraint 3: The person who has a cat is directly left of the person whose mother's name is Holly.
            if mothers_perm[idx_arnold + 1] != "Holly":
                continue

            # Iterate over possible assignments for pets.
            for pets_perm in itertools.permutations(pets_list):
                # Constraint 10: Arnold is the person who has a cat.
                if pets_perm[idx_arnold] != "cat":
                    continue
                # Constraint 5: Eric is the person who owns a rabbit.
                if pets_perm[idx_eric] != "rabbit":
                    continue
                # Constraint 4: The person with a pet hamster is directly left of the person who owns a rabbit.
                if pets_perm[idx_eric - 1] != "hamster":
                    continue
                # Constraint 6: There is one house between the person who owns a dog and the person who has a cat.
                try:
                    idx_dog = pets_perm.index("dog")
                except ValueError:
                    continue
                if abs(idx_dog - idx_arnold) != 2:
                    continue

                # Constraint 12: The person with an aquarium of fish is the person whose mother's name is Sarah.
                valid_fish = True
                for i in range(6):
                    if pets_perm[i] == "fish" and mothers_perm[i] != "Sarah":
                        valid_fish = False
                        break
                    if mothers_perm[i] == "Sarah" and pets_perm[i] != "fish":
                        valid_fish = False
                        break
                if not valid_fish:
                    continue

                # All constraints satisfied: build the solution.
                solution_rows = []
                for i in range(6):
                    house_num = str(i+1)
                    solution_rows.append([house_num, names_perm[i], mothers_perm[i], pets_perm[i]])
                result = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Pet"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(result))
                return

if __name__ == '__main__':
    main()