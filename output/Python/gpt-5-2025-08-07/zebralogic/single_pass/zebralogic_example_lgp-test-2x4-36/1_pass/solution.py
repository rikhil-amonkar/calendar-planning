import itertools
import json

def solve_zebra_puzzle():
    # Input variables
    houses = [1, 2]  # Left to right
    Names = ["Eric", "Arnold"]
    BookGenres = ["science fiction", "mystery"]
    Birthdays = ["april", "sept"]
    Animals = ["horse", "cat"]

    solutions = []

    # Generate all permutations for each category and filter by constraints
    for names_perm in itertools.permutations(Names):
        # Clue 1: Eric is in the first house.
        if names_perm[0] != "Eric":
            continue

        for books_perm in itertools.permutations(BookGenres):
            # Clue 3: The person who loves science fiction books is in the second house.
            if books_perm[1] != "science fiction":
                continue

            for bdays_perm in itertools.permutations(Birthdays):
                # Clue 2: Eric is the person whose birthday is in September.
                idx_eric = names_perm.index("Eric")
                if bdays_perm[idx_eric] != "sept":
                    continue

                for animals_perm in itertools.permutations(Animals):
                    # Clue 4: The person who keeps horses is the person whose birthday is in September.
                    consistent = True
                    for h in range(len(houses)):
                        is_horse = animals_perm[h] == "horse"
                        is_sept = bdays_perm[h] == "sept"
                        if is_horse != is_sept:
                            consistent = False
                            break
                    if not consistent:
                        continue

                    # If all constraints satisfied, record solution
                    solution = {
                        "houses": list(houses),
                        "names": list(names_perm),
                        "books": list(books_perm),
                        "birthdays": list(bdays_perm),
                        "animals": list(animals_perm),
                    }
                    solutions.append(solution)

    # Prepare output
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    # Assuming unique solution; take the first
    sol = solutions[0]
    header = ["House", "Name", "BookGenre", "Birthday", "Animal"]
    rows = []
    for i, house in enumerate(sol["houses"]):
        rows.append([
            str(house),
            sol["names"][i],
            sol["books"][i],
            sol["birthdays"][i],
            sol["animals"][i],
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_zebra_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))