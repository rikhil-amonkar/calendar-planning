#!/usr/bin/env python3
import json
import itertools

def main():
    # Define the attributes for each house
    names_all = ["Arnold", "Eric", "Peter"]
    cigars_all = ["pall mall", "blue master", "prince"]
    animals_all = ["horse", "cat", "bird"]
    children_all = ["Bella", "Fred", "Meredith"]
    books_all = ["science fiction", "romance", "mystery"]
    # Phones are fixed by constraints (see clue 6, 9, and 10)
    phones_fixed = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    # Iterate over all possible assignments using permutations
    for names_perm in itertools.permutations(names_all):
        for cigars_perm in itertools.permutations(cigars_all):
            # Clue 3: House 2 must have "pall mall"
            if cigars_perm[1] != "pall mall":
                continue
            for animals_perm in itertools.permutations(animals_all):
                for children_perm in itertools.permutations(children_all):
                    for books_perm in itertools.permutations(books_all):
                        # Clue 10: The person who loves science fiction is in the third house.
                        if books_perm[2] != "science fiction":
                            continue
                        # Clue 11: The person who loves mystery books is not in the second house.
                        if books_perm[1] == "mystery":
                            continue

                        valid = True
                        # Check house-by-house constraints:
                        for i in range(3):
                            # Clue 1: If a house's book is "mystery", then its child is named Fred.
                            if books_perm[i] == "mystery" and children_perm[i] != "Fred":
                                valid = False
                                break
                            # Clue 4: If a house's animal is "horse", then its child is named Meredith.
                            if animals_perm[i] == "horse" and children_perm[i] != "Meredith":
                                valid = False
                                break
                            # Clue 5: If a house's child is named Bella, then the person smokes "prince".
                            if children_perm[i] == "Bella" and cigars_perm[i] != "prince":
                                valid = False
                                break
                            # Clue 2: The cat lover is Eric.
                            if names_perm[i] == "Eric" and animals_perm[i] != "cat":
                                valid = False
                                break
                            # Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
                            if books_perm[i] == "science fiction" and phones_fixed[i] != "samsung galaxy s21":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 6: The person with iPhone 13 is directly left of the person with Samsung Galaxy S21.
                        found_phone_neighbor = False
                        for i in range(2):  # only possible for houses 1->2 or 2->3
                            if phones_fixed[i] == "iphone 13" and phones_fixed[i+1] == "samsung galaxy s21":
                                found_phone_neighbor = True
                                break
                        if not found_phone_neighbor:
                            continue

                        # Clue 7: The house whose child is named Fred is directly left of the house occupied by Arnold.
                        found_fred_arnold = False
                        for i in range(2):
                            if children_perm[i] == "Fred" and names_perm[i+1] == "Arnold":
                                found_fred_arnold = True
                                break
                        if not found_fred_arnold:
                            continue

                        # Clue 8: Peter is somewhere to the left of Eric.
                        pos_peter = names_perm.index("Peter")
                        pos_eric = names_perm.index("Eric")
                        if pos_peter >= pos_eric:
                            continue

                        # If all constraints are met, build and output the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Cigar", "Animal", "Child", "Book", "Phone"],
                                "rows": []
                            }
                        }
                        for i in range(3):
                            solution["solution"]["rows"].append([
                                str(i+1),
                                names_perm[i],
                                cigars_perm[i],
                                animals_perm[i],
                                children_perm[i],
                                books_perm[i],
                                phones_fixed[i]
                            ])
                        print(json.dumps(solution))
                        return

if __name__ == "__main__":
    main()