from z3 import *

# Define the variables
house = [Int(f'house_{i}') for i in range(1, 4)]
name = [Int(f'name_{i}') for i in range(1, 4)]
book_genre = [Int(f'book_genre_{i}') for i in range(1, 4)]
vacation = [Int(f'vacation_{i}') for i in range(1, 4)]

# Define the domains
names = {'Eric': 1, 'Arnold': 2, 'Peter': 3}
book_genres = {'mystery': 1, 'science fiction': 2, 'romance': 3}
vacations = {'mountain': 1, 'beach': 2, 'city': 3}

# Create the solver
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct(name))
solver.add(Distinct(book_genre))
solver.add(Distinct(vacation))

# Constraint 1: Eric is directly left of Arnold
eric_left_of_arnold = Or(
    And(name[0] == names['Eric'], name[1] == names['Arnold']),
    And(name[1] == names['Eric'], name[2] == names['Arnold'])
)
solver.add(eric_left_of_arnold)

# Constraint 2: Peter is somewhere to the right of the person who loves beach vacations
peter_right_of_beach = Or(
    And(vacation[1] == vacations['beach'], name[2] == names['Peter']),
    And(vacation[0] == vacations['beach'], Or(name[1] == names['Peter'], name[2] == names['Peter']))
)
solver.add(peter_right_of_beach)

# Constraint 3: Peter is the person who prefers city breaks
solver.add(vacation[name.index(names['Peter'])] == vacations['city'])

# Constraint 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations
mystery_left_of_beach = Or(
    And(book_genre[0] == book_genres['mystery'], vacation[1] == vacations['beach']),
    And(book_genre[0] == book_genres['mystery'], vacation[2] == vacations['beach']),
    And(book_genre[1] == book_genres['mystery'], vacation[2] == vacations['beach'])
)
solver.add(mystery_left_of_beach)

# Constraint 5: The person who loves science fiction books is the person who loves beach vacations
solver.add(book_genre[vacation.index(vacations['beach'])] == book_genres['science fiction'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": []
        }
    }
    for i in range(3):
        name_val = [k for k, v in names.items() if v == model.evaluate(name[i]).as_long()][0]
        book_genre_val = [k for k, v in book_genres.items() if v == model.evaluate(book_genre[i]).as_long()][0]
        vacation_val = [k for k, v in vacations.items() if v == model.evaluate(vacation[i]).as_long()][0]
        solution["solution"]["rows"].append([str(i+1), name_val, book_genre_val, vacation_val])
    
    print(solution)
else:
    print("No solution found")