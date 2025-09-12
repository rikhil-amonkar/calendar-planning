from z3 import *

def solve_puzzle():
    # Define the domain for each variable
    houses = range(1, 7)
    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    book_genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # Create dictionaries to map each attribute to a Z3 variable
    name_vars = {name: Int(f'name_{name}') for name in names}
    book_genre_vars = {genre: Int(f'genre_{genre}') for genre in book_genres}
    occupation_vars = {occupation: Int(f'occupation_{occupation}') for occupation in occupations}

    # Create a solver instance
    solver = Solver()

    # Add constraints for each attribute to be in a different house
    for var_dict in [name_vars, book_genre_vars, occupation_vars]:
        solver.add(Distinct(list(var_dict.values())))

    # Add constraints for each house number to be between 1 and 6
    for var in list(name_vars.values()) + list(book_genre_vars.values()) + list(occupation_vars.values()):
        solver.add(And(var >= 1, var <= 6))

    # Clue 1: Alice is the person who loves fantasy books.
    solver.add(name_vars["Alice"] == book_genre_vars["fantasy"])

    # Clue 2: The person who loves mystery books and Bob are next to each other.
    solver.add(Abs(book_genre_vars["mystery"] - name_vars["Bob"]) == 1)

    # Clue 3: Carol is the person who loves mystery books.
    solver.add(name_vars["Carol"] == book_genre_vars["mystery"])

    # Clue 4: The person who is a lawyer is the person who loves fantasy books.
    solver.add(occupation_vars["lawyer"] == book_genre_vars["fantasy"])

    # Clue 5: Bob is not in the fifth house.
    solver.add(name_vars["Bob"] != 5)

    # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
    solver.add(name_vars["Arnold"] < occupation_vars["engineer"])

    # Clue 7: The person who is a nurse is directly left of Alice.
    solver.add(occupation_vars["nurse"] + 1 == name_vars["Alice"])

    # Clue 8: The person who loves biography books is the person who is a teacher.
    solver.add(book_genre_vars["biography"] == occupation_vars["teacher"])

    # Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    solver.add(book_genre_vars["historical fiction"] < occupation_vars["teacher"])

    # Clue 10: The person who is a doctor is in the first house.
    solver.add(occupation_vars["doctor"] == 1)

    # Clue 11: The person who loves science fiction books is the person who is an artist.
    solver.add(book_genre_vars["science fiction"] == occupation_vars["artist"])

    # Clue 12: Eric is in the third house.
    solver.add(name_vars["Eric"] == 3)

    # Clue 13: The person who loves mystery books is not in the fifth house.
    solver.add(book_genre_vars["mystery"] != 5)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            name = next(name for name, var in name_vars.items() if model.evaluate(var).as_long() == house)
            book_genre = next(genre for genre, var in book_genre_vars.items() if model.evaluate(var).as_long() == house)
            occupation = next(occ for occ, var in occupation_vars.items() if model.evaluate(var).as_long() == house)
            solution.append([str(house), name, book_genre, occupation])

        return {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": solution
            }
        }
    else:
        return {"solution": None}

# Print the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))