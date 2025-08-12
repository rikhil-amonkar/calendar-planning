import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold", "Peter"]
    books = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]

    # Generate all possible permutations for each attribute
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(books)) * \
                   list(itertools.permutations(vacations))

    # Iterate through all combinations of permutations
    for name_perm in itertools.permutations(names):
        for book_perm in itertools.permutations(books):
            for vacation_perm in itertools.permutations(vacations):
                # Unpack the permutations
                name1, name2, name3 = name_perm
                book1, book2, book3 = book_perm
                vacation1, vacation2, vacation3 = vacation_perm

                # Check all the clues
                if (name1 == "Eric" and name2 == "Arnold" and  # Clue 1
                    (vacation2 == "beach" or vacation3 == "beach") and  # Clue 2
                    name3 == "Peter" and vacation3 == "city" and  # Clue 3
                    (book1 == "mystery" or book2 == "mystery") and (vacation2 == "beach" or vacation3 == "beach") and  # Clue 4
                    vacation2 == "beach" and book2 == "science fiction"):  # Clue 5

                    # Construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Favorite Book Genre", "Type of Vacation"],
                            "rows": [
                                ["1", name1, book1, vacation1],
                                ["2", name2, book2, vacation2],
                                ["3", name3, book3, vacation3]
                            ]
                        }
                    }

                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return

# Run the solver
solve_puzzle()