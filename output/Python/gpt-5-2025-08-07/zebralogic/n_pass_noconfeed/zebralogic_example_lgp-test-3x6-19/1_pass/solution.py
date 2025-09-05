import json
from itertools import permutations

def solve_puzzle():
    houses = [0, 1, 2]  # indices for houses 1..3

    Names = ['Arnold', 'Eric', 'Peter']
    Cigars = ['pall mall', 'blue master', 'prince']
    Animals = ['horse', 'cat', 'bird']
    Children = ['Bella', 'Fred', 'Meredith']
    Books = ['science fiction', 'romance', 'mystery']
    Phones = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']

    header = ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"]

    solutions = []

    for names in permutations(Names):
        # Clue 8: Peter is somewhere to the left of Eric.
        if names.index('Peter') >= names.index('Eric'):
            continue

        for cigars in permutations(Cigars):
            # Clue 3: Pall Mall is in the second house.
            if cigars[1] != 'pall mall':
                continue

            for animals in permutations(Animals):
                # Clue 2: The cat lover is Eric.
                if animals.index('cat') != names.index('Eric'):
                    continue

                for children in permutations(Children):
                    # Clue 5: Bella <-> Prince
                    if children.index('Bella') != cigars.index('prince'):
                        continue

                    # Clue 4: Horse <-> Meredith
                    if animals.index('horse') != children.index('Meredith'):
                        continue

                    # Clue 7: Fred is directly left of Arnold.
                    if children.index('Fred') + 1 != names.index('Arnold'):
                        continue

                    for books in permutations(Books):
                        # Clue 10: Sci-fi is in the third house.
                        if books[2] != 'science fiction':
                            continue

                        # Clue 11: Mystery is not in the second house.
                        if books[1] == 'mystery':
                            continue

                        # Clue 1: Mystery <-> Fred
                        if books.index('mystery') != children.index('Fred'):
                            continue

                        for phones in permutations(Phones):
                            # Clue 6: iPhone 13 is directly left of Samsung Galaxy S21.
                            if phones.index('iphone 13') + 1 != phones.index('samsung galaxy s21'):
                                continue

                            # Clue 9: Sci-fi <-> Samsung Galaxy S21
                            if books.index('science fiction') != phones.index('samsung galaxy s21'):
                                continue

                            # All constraints satisfied, record solution
                            rows = []
                            for h in houses:
                                rows.append([
                                    str(h + 1),
                                    names[h],
                                    cigars[h],
                                    animals[h],
                                    children[h],
                                    books[h],
                                    phones[h]
                                ])
                            solutions.append(rows)

    # Expect exactly one solution
    if not solutions:
        raise RuntimeError("No solution found.")
    # Use the first (and should be unique) solution
    rows = solutions[0]

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))