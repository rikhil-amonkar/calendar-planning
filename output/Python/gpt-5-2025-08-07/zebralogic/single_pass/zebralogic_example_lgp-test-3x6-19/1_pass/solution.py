import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3]

    names = ["Arnold", "Eric", "Peter"]
    cigars = ["pall mall", "blue master", "prince"]
    animals = ["horse", "cat", "bird"]
    children = ["Bella", "Fred", "Meredith"]
    books = ["science fiction", "romance", "mystery"]
    phones = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    solutions = []

    for perm_names in permutations(names):
        # Clue 8: Peter is somewhere to the left of Eric.
        if perm_names.index("Peter") >= perm_names.index("Eric"):
            continue

        for perm_cigars in permutations(cigars):
            # Clue 3: Pall Mall is in the second house.
            if perm_cigars[1] != "pall mall":
                continue

            for perm_animals in permutations(animals):
                # Clue 2: The cat lover is Eric.
                if perm_animals.index("cat") != perm_names.index("Eric"):
                    continue

                for perm_children in permutations(children):
                    # Clue 4: The person who keeps horses has child Meredith.
                    if perm_animals.index("horse") != perm_children.index("Meredith"):
                        continue

                    # Clue 5: The person's child Bella is the Prince smoker.
                    if perm_children.index("Bella") != perm_cigars.index("prince"):
                        continue

                    # Clue 7: Fred is directly left of Arnold.
                    if perm_children.index("Fred") + 1 != perm_names.index("Arnold"):
                        continue

                    for perm_books in permutations(books):
                        # Clue 1: The mystery lover has child Fred.
                        if perm_books.index("mystery") != perm_children.index("Fred"):
                            continue

                        # Clue 10: Science fiction is in the third house.
                        if perm_books[2] != "science fiction":
                            continue

                        # Clue 11: The mystery lover is not in the second house.
                        if perm_books[1] == "mystery":
                            continue

                        for perm_phones in permutations(phones):
                            # Clue 6: iPhone 13 is directly left of Samsung Galaxy S21.
                            if perm_phones.index("iphone 13") + 1 != perm_phones.index("samsung galaxy s21"):
                                continue

                            # Clue 9: Science fiction lover uses Samsung Galaxy S21.
                            if perm_books.index("science fiction") != perm_phones.index("samsung galaxy s21"):
                                continue

                            rows = []
                            for i in range(3):
                                rows.append([
                                    str(i + 1),
                                    perm_names[i],
                                    perm_cigars[i],
                                    perm_animals[i],
                                    perm_children[i],
                                    perm_books[i],
                                    perm_phones[i],
                                ])
                            solutions.append(rows)

    if not solutions:
        raise RuntimeError("No solution found.")

    # Assuming a unique solution; take the first.
    solution = solutions[0]
    result = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
            "rows": solution
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))