from z3 import *

# Define the variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_book_genre = String('house1_book_genre')
house2_book_genre = String('house2_book_genre')
house1_birthday = String('house1_birthday')
house2_birthday = String('house2_birthday')
house1_animal = String('house1_animal')
house2_animal = String('house2_animal')

# Define the domains
names = ['Eric', 'Arnold']
book_genres = ['science fiction', 'mystery']
birthdays = ['april', 'sept']
animals = ['horse', 'cat']

# Create the solver
solver = Solver()

# Add constraints for uniqueness
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_book_genre, house2_book_genre))
solver.add(Distinct(house1_birthday, house2_birthday))
solver.add(Distinct(house1_animal, house2_animal))

# Add constraints based on the clues
solver.add(house1_name == 'Eric')
solver.add(house1_birthday == 'sept')
solver.add(house2_book_genre == 'science fiction')
solver.add(house1_birthday == 'sept')
solver.add(house1_animal == 'horse')

# Add domain constraints
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house1_book_genre == 'science fiction', house1_book_genre == 'mystery'))
solver.add(Or(house2_book_genre == 'science fiction', house2_book_genre == 'mystery'))
solver.add(Or(house1_birthday == 'april', house1_birthday == 'sept'))
solver.add(Or(house2_birthday == 'april', house2_birthday == 'sept'))
solver.add(Or(house1_animal == 'horse', house1_animal == 'cat'))
solver.add(Or(house2_animal == 'horse', house2_animal == 'cat'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_book_genre].as_string(), model[house1_birthday].as_string(), model[house1_animal].as_string()],
                ["2", model[house2_name].as_string(), model[house2_book_genre].as_string(), model[house2_birthday].as_string(), model[house2_animal].as_string()]
            ]
        }
    }
    import json
    print(json.dumps(solution))
else:
    print("No solution found")