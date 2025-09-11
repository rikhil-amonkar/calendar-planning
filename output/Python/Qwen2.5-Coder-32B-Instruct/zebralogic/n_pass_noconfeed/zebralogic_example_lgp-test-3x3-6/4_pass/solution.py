import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold", "Peter"]
    book_genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]

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
        if (peter == city and  # Constraint 3: Peter goes to the city
                vacation_perm.index(beach) > book_genre_perm.index(mystery) and  # Constraint 4: Mystery reader goes before beach vacationer
                science_fiction == beach):  # Constraint 5: Science fiction reader goes to the beach
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