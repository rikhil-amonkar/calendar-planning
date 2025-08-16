from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_book_genre = String('house1_book_genre')
house2_book_genre = String('house2_book_genre')

# Define domains for the variables
names = ['Eric', 'Arnold']
book_genres = ['science fiction', 'mystery']

# Add constraints for unique names and book genres
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_book_genre, house2_book_genre))

# Add constraints based on the clues
solver.add(house1_name == 'Eric')
solver.add(house2_book_genre == 'mystery')

# Check if the problem is solvable
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
    print(solution)
else:
    print("No solution found")