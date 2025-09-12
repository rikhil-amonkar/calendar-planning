from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_book_genre = String('house1_book_genre')
house2_book_genre = String('house2_book_genre')

# Create the solver
solver = Solver()

# Define the domains for the variables
names = ['Eric', 'Arnold']
book_genres = ['science fiction', 'mystery']

# Add constraints for unique names and book genres
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_book_genre, house2_book_genre))

# Add constraints for the domain of each variable
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house1_book_genre == 'science fiction', house1_book_genre == 'mystery'))
solver.add(Or(house2_book_genre == 'science fiction', house2_book_genre == 'mystery'))

# Add the clue constraint
solver.add(And(house1_name == 'Eric', house2_book_genre == 'mystery'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_book_genre].as_string()],
                ["2", model[house2_name].as_string(), model[house2_book_genre].as_string()]
            ]
        }
    }
    print(json.dumps(solution))
else:
    print("No solution found")