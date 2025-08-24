import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]

    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthdays = ["april", "sept"]

    solutions = []

    # Iterate over all permutations for each category (assignments per house)
    for books_perm in itertools.permutations(book_genres):
        # Clue 5: The person who loves mystery books is in the first house.
        if books_perm[0] != "mystery":
            continue

        for music_perm in itertools.permutations(music_genres):
            # Clue 1: mystery <-> rock (same person)
            ok = True
            for i in range(2):
                if (books_perm[i] == "mystery") != (music_perm[i] == "rock"):
                    ok = False
                    break
            if not ok:
                continue

            for hobby_perm in itertools.permutations(hobbies):
                # Clue 3: mystery <-> gardening (same person)
                ok = True
                for i in range(2):
                    if (books_perm[i] == "mystery") != (hobby_perm[i] == "gardening"):
                        ok = False
                        break
                if not ok:
                    continue

                for name_perm in itertools.permutations(names):
                    # Clue 2: Arnold is not in the first house.
                    if name_perm[0] == "Arnold":
                        continue

                    for bday_perm in itertools.permutations(birthdays):
                        # Clue 4: April <-> Arnold (same person)
                        ok = True
                        for i in range(2):
                            if (bday_perm[i] == "april") != (name_perm[i] == "Arnold"):
                                ok = False
                                break
                        if not ok:
                            continue

                        # If all constraints satisfied, record solution
                        solution = []
                        for i, house in enumerate(houses):
                            solution.append({
                                "House": str(house),
                                "Name": name_perm[i],
                                "Hobby": hobby_perm[i],
                                "BookGenre": books_perm[i],
                                "MusicGenre": music_perm[i],
                                "Birthday": bday_perm[i],
                            })
                        solutions.append(solution)

    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assuming unique solution; take the first
    sol = solutions[0]

    # Prepare JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": [
                [row["House"], row["Name"], row["Hobby"], row["BookGenre"], row["MusicGenre"], row["Birthday"]]
                for row in sorted(sol, key=lambda r: int(r["House"]))
            ]
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))