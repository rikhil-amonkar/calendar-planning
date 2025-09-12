import json
from z3 import *

def solve_puzzle():
    solver = Solver()

    # Variables for house 1
    name1 = String('name1')
    book1 = String('book1')
    birth1 = String('birth1')
    animal1 = String('animal1')

    # Variables for house 2
    name2 = String('name2')
    book2 = String('book2')
    birth2 = String('birth2')
    animal2 = String('animal2')

    # Add domain constraints for names
    solver.add(Or(name1 == 'Eric', name1 == 'Arnold'))
    solver.add(Or(name2 == 'Eric', name2 == 'Arnold'))
    solver.add(name1 != name2)

    # Add domain constraints for book genres
    solver.add(Or(book1 == 'science fiction', book1 == 'mystery'))
    solver.add(Or(book2 == 'science fiction', book2 == 'mystery'))
    solver.add(book1 != book2)

    # Add domain constraints for birthdays
    solver.add(Or(birth1 == 'april', birth1 == 'sept'))
    solver.add(Or(birth2 == 'april', birth2 == 'sept'))
    solver.add(birth1 != birth2)

    # Add domain constraints for animals
    solver.add(Or(animal1 == 'horse', animal1 == 'cat'))
    solver.add(Or(animal2 == 'horse', animal2 == 'cat'))
    solver.add(animal1 != animal2)

    # Add puzzle-specific constraints
    solver.add(name1 == 'Eric')  # Clue 1
    solver.add(birth1 == 'sept')  # Clue 2
    solver.add(book2 == 'science fiction')  # Clue 3
    solver.add(Implies(animal1 == 'horse', birth1 == 'sept'))  # Clue 4 part 1
    solver.add(Implies(animal2 == 'horse', birth2 == 'sept'))  # Clue 4 part 2

    # Check for solution
    if solver.check() == sat:
        model = solver.model()

        # Extract values for house 1
        n1 = model.eval(name1).as_string()
        b1 = model.eval(book1).as_string()
        br1 = model.eval(birth1).as_string()
        a1 = model.eval(animal1).as_string()

        # Extract values for house 2
        n2 = model.eval(name2).as_string()
        b2 = model.eval(book2).as_string()
        br2 = model.eval(birth2).as_string()
        a2 = model.eval(animal2).as_string()

        # Build the JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                "rows": [
                    ["1", n1, b1, br1, a1],
                    ["2", n2, b2, br2, a2]
                ]
            }
        }

        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

# Run the function and print the result
print(solve_puzzle())