from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_genre = String('house1_genre')
house2_genre = String('house2_genre')

# Define domains
names = ['Eric', 'Arnold']
genres = ['science fiction', 'mystery']

# Constraints for unique names and genres per house
solver.add(house1_name != house2_name)
solver.add(house1_genre != house2_genre)

# Constraint for names
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))

# Constraint for genres
solver.add(Or(house1_genre == 'science fiction', house1_genre == 'mystery'))
solver.add(Or(house2_genre == 'science fiction', house2_genre == 'mystery'))

# Clue constraint: Eric is directly left of the person who loves mystery books
solver.add(Implies(house1_name == 'Eric', house2_genre == 'mystery'))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution_house1_name = model[house1_name].as_string()[1:-1]  # Remove quotes
    solution_house2_name = model[house2_name].as_string()[1:-1]  # Remove quotes
    solution_house1_genre = model[house1_genre].as_string()[1:-1]  # Remove quotes
    solution_house2_genre = model[house2_genre].as_string()[1:-1]  # Remove quotes
    
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": [
                ["1", solution_house1_name, solution_house1_genre],
                ["2", solution_house2_name, solution_house2_genre]
            ]
        }
    }
    
    print(solution)
else:
    print("No solution found")