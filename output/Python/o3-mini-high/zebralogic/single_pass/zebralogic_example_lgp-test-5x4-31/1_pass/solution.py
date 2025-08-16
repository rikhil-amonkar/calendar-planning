#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations = ["cruise", "city", "camping", "beach", "mountain"]
    children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities = ["dane", "norwegian", "brit", "german", "swede"]

    # We have 5 houses: indices 0..4 correspond to houses 1..5.
    solution = None

    # Iterate over all permutations for names.
    for names_perm in itertools.permutations(names):
        # Clue 8: Eric is not in the 5th house (index4).
        if names_perm[4] == "Eric":
            continue

        # Iterate over vacations and enforce clue 6:
        # The person who likes cruises is in the first house (index0 must be "cruise").
        for vac_perm in itertools.permutations(vacations):
            if vac_perm[0] != "cruise":
                continue

            # Clue 11: Bob is the person who enjoys camping.
            valid_bob = True
            for i in range(5):
                if names_perm[i] == "Bob" and vac_perm[i] != "camping":
                    valid_bob = False
                    break
            if not valid_bob:
                continue

            # Clue 13: The person who enjoys camping trips is not in the fifth house.
            if vac_perm[4] == "camping":
                continue

            # Iterate over children permutations.
            for child_perm in itertools.permutations(children):
                # Clue 7: The person's child is named Meredith is in the fourth house (index3).
                if child_perm[3] != "Meredith":
                    continue
                # Clue 4: The person's child is named Bella is not in the second house (index1).
                if child_perm[1] == "Bella":
                    continue

                # Iterate over nationalities permutations.
                for nat_perm in itertools.permutations(nationalities):
                    # Clue 12: The Dane is in the fifth house (index4).
                    if nat_perm[4] != "dane":
                        continue

                    valid = True

                    # Clue 1: The Norwegian is Peter.
                    for i in range(5):
                        if nat_perm[i] == "norwegian" and names_perm[i] != "Peter":
                            valid = False
                            break
                        if names_perm[i] == "Peter" and nat_perm[i] != "norwegian":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 5: Alice is the British person.
                    for i in range(5):
                        if names_perm[i] == "Alice" and nat_perm[i] != "brit":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 9: The Swedish person is somewhere to the right of the Norwegian.
                    pos_nor = None
                    pos_swede = None
                    for i in range(5):
                        if nat_perm[i] == "norwegian":
                            pos_nor = i
                        if nat_perm[i] == "swede":
                            pos_swede = i
                    if pos_nor is None or pos_swede is None or pos_swede <= pos_nor:
                        continue

                    # Clue 2: The Swedish person is the one whose child is named Bella.
                    for i in range(5):
                        if nat_perm[i] == "swede" and child_perm[i] != "Bella":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 3: The person who loves beach vacations is directly left of the person whose child is named Samantha.
                    beach_pair_found = False
                    for i in range(4):
                        if vac_perm[i] == "beach" and child_perm[i+1] == "Samantha":
                            beach_pair_found = True
                            break
                    if not beach_pair_found:
                        continue

                    # Clue 10: There is one house between the person whose child is named Fred and the person who prefers city breaks.
                    try:
                        pos_fred = child_perm.index("Fred")
                        pos_city = vac_perm.index("city")
                    except ValueError:
                        continue
                    if abs(pos_fred - pos_city) != 2:
                        continue

                    # All clues satisfied so record solution.
                    solution = []
                    for i in range(5):
                        solution.append([str(i+1), names_perm[i], vac_perm[i], child_perm[i], nat_perm[i]])
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": solution
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()