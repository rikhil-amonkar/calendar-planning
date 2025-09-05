import itertools
import json

def solve_puzzle():
    # Puzzle parameters
    houses = [1, 2]  # Left to right
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]

    solutions = []

    # Iterate over all permutations for each attribute category
    for name_assign in itertools.permutations(names, len(houses)):
        for book_assign in itertools.permutations(book_genres, len(houses)):
            # Clue 5: The person who loves mystery books is in the first house.
            if book_assign[0] != "mystery":
                continue

            for vacation_assign in itertools.permutations(vacations, len(houses)):
                # Clue 1: The person who loves beach vacations is Eric.
                try:
                    idx_beach = vacation_assign.index("beach")
                except ValueError:
                    continue
                if name_assign[idx_beach] != "Eric":
                    continue

                for animal_assign in itertools.permutations(animals, len(houses)):
                    # Clue 4: The cat lover is not in the second house.
                    if animal_assign[1] == "cat":
                        continue

                    for music_assign in itertools.permutations(music_genres, len(houses)):
                        # Clue 2: The person who loves pop music is the person who loves beach vacations.
                        try:
                            idx_pop = music_assign.index("pop")
                        except ValueError:
                            continue
                        if idx_pop != idx_beach:
                            continue

                        # Clue 3: The person who loves rock music is the person who loves mystery books.
                        try:
                            idx_rock = music_assign.index("rock")
                            idx_mystery = book_assign.index("mystery")
                        except ValueError:
                            continue
                        if idx_rock != idx_mystery:
                            continue

                        # All constraints satisfied; record solution
                        solution_rows = []
                        for i, house in enumerate(houses):
                            row = [
                                str(house),
                                name_assign[i],
                                book_assign[i],
                                vacation_assign[i],
                                animal_assign[i],
                                music_assign[i],
                            ]
                            solution_rows.append(row)
                        solutions.append(solution_rows)

    if not solutions:
        raise ValueError("No solution found.")

    # Assuming a unique solution; take the first
    solution_rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()