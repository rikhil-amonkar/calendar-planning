import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold", "Peter"]
    book_genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(book_genres)) * \
                   list(itertools.permutations(vacations))

    # Iterate over all possible combinations of permutations
    for name_perm in itertools.permutations(names):
        for book_genre_perm in itertools.permutations(book_genres):
            for vacation_perm in itertools.permutations(vacations):
                # Unpack the permutations into individual lists
                name1, name2, name3 = name_perm
                book_genre1, book_genre2, book_genre3 = book_genre_perm
                vacation1, vacation2, vacation3 = vacation_perm

                # Apply the clues to check if the current combination is valid
                if (name1 == "Eric" and name2 == "Arnold" and  # Clue 1
                    (vacation2 == "beach" and name3 == "Peter") or  # Clue 2
                    (vacation1 == "beach" and name3 == "Peter") and  # Clue 2
                    name3 == "Peter" and vacation3 == "city" and  # Clue 3
                    (book_genre1 == "mystery" and vacation2 == "beach") or  # Clue 4
                    (book_genre1 == "mystery" and vacation3 == "beach") and  # Clue 4
                    book_genre3 == "science fiction" and vacation3 == "beach"):  # Clue 5
                    # If all clues are satisfied, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "BookGenre", "Vacation"],
                            "rows": [
                                ["1", name1, book_genre1, vacation1],
                                ["2", name2, book_genre2, vacation2],
                                ["3", name3, book_genre3, vacation3]
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution as JSON
print(solve_puzzle())