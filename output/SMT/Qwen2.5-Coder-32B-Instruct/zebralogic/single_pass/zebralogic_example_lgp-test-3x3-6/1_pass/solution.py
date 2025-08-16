from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3]
names = ['Eric', 'Arnold', 'Peter']
book_genres = ['mystery', 'science fiction', 'romance']
vacations = ['mountain', 'beach', 'city']

# Declare variables for each characteristic
name_vars = {house: Int(f'name_{house}') for house in houses}
book_genre_vars = {house: Int(f'book_genre_{house}') for house in houses}
vacation_vars = {house: Int(f'vacation_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([book_genre_vars[house] for house in houses]))
solver.add(Distinct([vacation_vars[house] for house in houses]))

# Map string values to integer codes
name_map = {name: i for i, name in enumerate(names)}
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}
vacation_map = {vacation: i for i, vacation in enumerate(vacations)}

# Add constraints based on clues
# Clue 1: Eric is directly left of Arnold.
solver.add(name_vars[1] == name_map['Eric'])
solver.add(name_vars[2] == name_map['Arnold'])

# Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
solver.add(Or(
    And(vacation_vars[1] != vacation_map['beach'], name_vars[2] == name_map['Peter']),
    And(vacation_vars[1] != vacation_map['beach'], vacation_vars[2] != vacation_map['beach'], name_vars[3] == name_map['Peter'])
))

# Clue 3: Peter is the person who prefers city breaks.
solver.add(vacation_vars[name_map['Peter']] == vacation_map['city'])

# Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
solver.add(Or(
    And(book_genre_vars[1] == book_genre_map['mystery'], vacation_vars[2] == vacation_map['beach']),
    And(book_genre_vars[1] == book_genre_map['mystery'], vacation_vars[3] == vacation_map['beach']),
    And(book_genre_vars[2] == book_genre_map['mystery'], vacation_vars[3] == vacation_map['beach'])
))

# Clue 5: The person who loves science fiction books is the person who loves beach vacations.
solver.add(book_genre_vars[vacation_map['beach']] == book_genre_map['science fiction'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": []
        }
    }
    
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        book_genre = book_genres[model.evaluate(book_genre_vars[house]).as_long()]
        vacation = vacations[model.evaluate(vacation_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, book_genre, vacation])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")