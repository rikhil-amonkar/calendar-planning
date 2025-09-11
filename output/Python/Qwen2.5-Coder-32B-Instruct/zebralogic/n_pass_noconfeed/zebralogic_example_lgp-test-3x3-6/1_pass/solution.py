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

    # Iterate over all possible combinations
    for name_perm, book_genre_perm, vacation_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(book_genres),
            itertools.permutations(vacations)
    ):
        # Unpack the permutations
        eric, arnold, peter = name_perm
        mystery, science_fiction, romance = book_genre_perm
        mountain, beach, city = vacation_perm

        # Check the constraints
        if (eric == name_perm[0] and arnold == name_perm[1] and  # Constraint 1
                peter == name_perm[2] and                       # Constraint 2
                peter == city and                             # Constraint 3
                mystery < beach and                           # Constraint 4
                science_fiction == beach):                      # Constraint 5
            # Create the solution dictionary
            solution = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Vacation"],
                    "rows": [
                        ["1", eric, mystery, mountain],
                        ["2", arnold, science_fiction, beach],
                        ["3", peter, romance, city]
                    ]
                }
            }
            # Print the solution as JSON
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()