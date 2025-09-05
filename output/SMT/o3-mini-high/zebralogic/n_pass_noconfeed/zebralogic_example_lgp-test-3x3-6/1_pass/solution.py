import json
from z3 import *

def main():
    solver = Solver()

    # Define variables for the house positions (1, 2, 3) for each attribute.
    Eric = Int('Eric')
    Arnold = Int('Arnold')
    Peter = Int('Peter')

    mystery = Int('mystery')
    science_fiction = Int('science_fiction')
    romance = Int('romance')

    mountain = Int('mountain')
    beach = Int('beach')
    city = Int('city')

    houses = [1, 2, 3]
    # Domain constraints: each variable must be one of the house numbers.
    for var in [Eric, Arnold, Peter, mystery, science_fiction, romance, mountain, beach, city]:
        solver.add(Or([var == h for h in houses]))

    # All-different constraints for each group.
    solver.add(Distinct(Eric, Arnold, Peter))
    solver.add(Distinct(mystery, science_fiction, romance))
    solver.add(Distinct(mountain, beach, city))

    # Clue 1: Eric is directly left of Arnold.
    solver.add(Eric + 1 == Arnold)

    # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
    solver.add(Peter > beach)

    # Clue 3: Peter is the person who prefers city breaks.
    solver.add(Peter == city)

    # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
    solver.add(mystery < beach)

    # Clue 5: The person who loves science fiction books is the person who loves beach vacations.
    solver.add(science_fiction == beach)

    if solver.check() == sat:
        model = solver.model()
        # Build mapping of house numbers to attributes.
        rows = []
        for h in houses:
            # Determine the Name for house h.
            if model[Eric].as_long() == h:
                name = "Eric"
            elif model[Arnold].as_long() == h:
                name = "Arnold"
            elif model[Peter].as_long() == h:
                name = "Peter"
            else:
                name = None

            # Determine the BookGenre for house h.
            if model[mystery].as_long() == h:
                book_genre = "mystery"
            elif model[science_fiction].as_long() == h:
                book_genre = "science fiction"
            elif model[romance].as_long() == h:
                book_genre = "romance"
            else:
                book_genre = None

            # Determine the Vacation for house h.
            if model[mountain].as_long() == h:
                vacation = "mountain"
            elif model[beach].as_long() == h:
                vacation = "beach"
            elif model[city].as_long() == h:
                vacation = "city"
            else:
                vacation = None

            rows.append([str(h), name, book_genre, vacation])

        result = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        # No solution found (should not happen with this puzzle)
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()