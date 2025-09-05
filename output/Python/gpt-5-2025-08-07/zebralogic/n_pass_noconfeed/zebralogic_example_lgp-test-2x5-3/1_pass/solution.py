import itertools
import json

def solve_puzzle():
    # Define the puzzle parameters
    houses = [1, 2]  # House numbers from left to right
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthdays = ["april", "sept"]

    # Helper to get index of a value in a list
    def idx(lst, value):
        return lst.index(value)

    solutions = []

    # Try all permutations for each category
    for name_perm in itertools.permutations(names):
        # Clue 2: Arnold is not in the first house.
        if name_perm[0] == "Arnold":
            continue

        for hobby_perm in itertools.permutations(hobbies):
            for book_perm in itertools.permutations(book_genres):
                # Clue 5: The person who loves mystery books is in the first house.
                if idx(book_perm, "mystery") != 0:
                    continue

                for music_perm in itertools.permutations(music_genres):
                    # Clue 1: Mystery books person is the rock music person.
                    if idx(book_perm, "mystery") != idx(music_perm, "rock"):
                        continue

                    for bday_perm in itertools.permutations(birthdays):
                        # Clue 4: The person whose birthday is in April is Arnold.
                        if idx(bday_perm, "april") != idx(name_perm, "Arnold"):
                            continue

                        # Clue 3: Mystery books person enjoys gardening.
                        if idx(book_perm, "mystery") != idx(hobby_perm, "gardening"):
                            continue

                        # All constraints satisfied; record the solution
                        solution_rows = []
                        for i, house in enumerate(houses):
                            row = [
                                str(house),
                                name_perm[i],
                                hobby_perm[i],
                                book_perm[i],
                                music_perm[i],
                                bday_perm[i],
                            ]
                            solution_rows.append(row)

                        solutions.append(solution_rows)

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Assuming unique solution; take the first
    rows = solutions[0]
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))