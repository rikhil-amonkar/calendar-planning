from z3 import *

def solve_puzzle():
    # Define the domains
    houses = [1, 2, 3]
    names = ["Arnold", "Eric", "Peter"]
    cigars = ["pall mall", "blue master", "prince"]
    animals = ["horse", "cat", "bird"]
    children = ["Bella", "Fred", "Meredith"]
    book_genres = ["science fiction", "romance", "mystery"]
    phone_models = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    # Create variables
    name_vars = {h: Int(f"name_{h}") for h in houses}
    cigar_vars = {h: Int(f"cigar_{h}") for h in houses}
    animal_vars = {h: Int(f"animal_{h}") for h in houses}
    child_vars = {h: Int(f"child_{h}") for h in houses}
    book_genre_vars = {h: Int(f"book_genre_{h}") for h in houses}
    phone_model_vars = {h: Int(f"phone_model_{h}") for h in houses}

    # Create solver
    solver = Solver()

    # Add domain constraints
    for h in houses:
        solver.add(name_vars[h] >= 0)
        solver.add(name_vars[h] < len(names))
        solver.add(cigar_vars[h] >= 0)
        solver.add(cigar_vars[h] < len(cigars))
        solver.add(animal_vars[h] >= 0)
        solver.add(animal_vars[h] < len(animals))
        solver.add(child_vars[h] >= 0)
        solver.add(child_vars[h] < len(children))
        solver.add(book_genre_vars[h] >= 0)
        solver.add(book_genre_vars[h] < len(book_genres))
        solver.add(phone_model_vars[h] >= 0)
        solver.add(phone_model_vars[h] < len(phone_models))

    # All values must be unique
    solver.add(Distinct([name_vars[h] for h in houses]))
    solver.add(Distinct([cigar_vars[h] for h in houses]))
    solver.add(Distinct([animal_vars[h] for h in houses]))
    solver.add(Distinct([child_vars[h] for h in houses]))
    solver.add(Distinct([book_genre_vars[h] for h in houses]))
    solver.add(Distinct([phone_model_vars[h] for h in houses]))

    # Clue constraints
    solver.add(And(book_genre_vars[h] == book_genres.index("mystery"), child_vars[h] == children.index("Fred")) for h in houses)
    solver.add(animal_vars[2] == animals.index("cat"))
    solver.add(cigar_vars[2] == cigars.index("pall mall"))
    solver.add(And(animal_vars[h] == animals.index("horse"), child_vars[h] == children.index("Meredith")) for h in houses)
    solver.add(And(child_vars[h] == children.index("Bella"), cigar_vars[h] == cigars.index("prince")) for h in houses)
    solver.add(phone_model_vars[1] == phone_models.index("iphone 13"))
    solver.add(phone_model_vars[2] == phone_models.index("samsung galaxy s21"))
    solver.add(child_vars[h] == children.index("Fred") == name_vars[h + 1] == names.index("Arnold") for h in [1])
    solver.add(name_vars[h] == names.index("Peter") < name_vars[h + 1] == names.index("Eric") for h in [1, 2])
    solver.add(book_genre_vars[3] == book_genres.index("science fiction"))
    solver.add(phone_model_vars[3] == phone_models.index("samsung galaxy s21"))
    solver.add(book_genre_vars[2] != book_genres.index("mystery"))

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for h in houses:
            name = names[model[name_vars[h]].as_long()]
            cigar = cigars[model[cigar_vars[h]].as_long()]
            animal = animals[model[animal_vars[h]].as_long()]
            child = children[model[child_vars[h]].as_long()]
            book_genre = book_genres[model[book_genre_vars[h]].as_long()]
            phone_model = phone_models[model[phone_model_vars[h]].as_long()]
            solution.append([str(h), name, cigar, animal, child, book_genre, phone_model])

        return {
            "solution": {
                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                "rows": solution
            }
        }
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))