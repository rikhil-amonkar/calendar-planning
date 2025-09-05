import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    birthdays = ["april", "sept"]
    animals = ["horse", "cat"]

    solutions = []

    # Enumerate all possible assignments with constraints
    for name_perm in itertools.permutations(names):
        # Clue 1: Eric is in the first house.
        if name_perm[0] != "Eric":
            continue

        for book_perm in itertools.permutations(book_genres):
            # Clue 3: The person who loves science fiction books is in the second house.
            if book_perm[1] != "science fiction":
                continue

            for birthday_perm in itertools.permutations(birthdays):
                # Clue 2: Eric is the person whose birthday is in September.
                eric_index = name_perm.index("Eric")
                if birthday_perm[eric_index] != "sept":
                    continue

                for animal_perm in itertools.permutations(animals):
                    # Clue 4: The person who keeps horses is the person whose birthday is in September.
                    sept_index = birthday_perm.index("sept")
                    if animal_perm[sept_index] != "horse":
                        continue

                    # Build solution mapping for houses
                    rows = []
                    for i, h in enumerate(houses):
                        rows.append([
                            str(h),
                            name_perm[i],
                            book_perm[i],
                            birthday_perm[i],
                            animal_perm[i],
                        ])

                    solutions.append(rows)

    if not solutions:
        raise ValueError("No solution found for the given constraints.")

    # Assuming a unique solution for this puzzle
    final_rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": final_rows
        }
    }

    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))