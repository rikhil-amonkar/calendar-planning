#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Eric", "Arnold", "Peter"]
    book_genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]

    solution = None

    for perm_names in itertools.permutations(names):
        # Constraint 1: Eric is directly left of Arnold.
        pos_eric = perm_names.index("Eric")
        pos_arnold = perm_names.index("Arnold")
        if pos_eric + 1 != pos_arnold:
            continue

        for perm_books in itertools.permutations(book_genres):
            for perm_vacations in itertools.permutations(vacations):
                # Constraint 3: Peter is the person who prefers city breaks.
                pos_peter = perm_names.index("Peter")
                if perm_vacations[pos_peter] != "city":
                    continue

                # Constraint 2: Peter is somewhere to the right of the person who loves beach vacations.
                try:
                    pos_beach = perm_vacations.index("beach")
                except ValueError:
                    continue
                if pos_beach >= pos_peter:
                    continue

                # Constraint 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
                pos_mystery = perm_books.index("mystery")
                if pos_mystery >= pos_beach:
                    continue

                # Constraint 5: The person who loves science fiction books is the person who loves beach vacations.
                pos_scifi = perm_books.index("science fiction")
                if perm_vacations[pos_scifi] != "beach":
                    continue

                # If all constraints are satisfied, record the solution.
                solution = []
                for i in range(3):
                    house = str(i + 1)
                    row = {
                        "House": house,
                        "Name": perm_names[i],
                        "Book genre": perm_books[i],
                        "Vacation": perm_vacations[i]
                    }
                    solution.append(row)
                break
            if solution:
                break
        if solution:
            break

    header = ["House", "Name", "Book genre", "Vacation"]
    rows = []
    # Ensure the houses are in order (house 1, then 2, then 3)
    for entry in solution:
        row = [entry["House"], entry["Name"], entry["Book genre"], entry["Vacation"]]
        rows.append(row)
    
    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output))

if __name__ == '__main__':
    main()