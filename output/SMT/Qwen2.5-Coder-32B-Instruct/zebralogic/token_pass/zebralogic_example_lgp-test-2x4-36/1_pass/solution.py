from z3 import *

# Define variables
house1_name = String('house1_name')
house1_book_genre = String('house1_book_genre')
house1_birthday = String('house1_birthday')
house1_animal = String('house1_animal')

house2_name = String('house2_name')
house2_book_genre = String('house2_book_genre')
house2_birthday = String('house2_birthday')
house2_animal = String('house2_animal')

# Define the domain of possible values
names = ['Eric', 'Arnold']
book_genres = ['science fiction', 'mystery']
birthdays = ['april', 'sept']
animals = ['horse', 'cat']

# Create the solver
solver = Solver()

# Add constraints based on the clues
# Clue 1: Eric is in the first house
solver.add(house1_name == 'Eric')

# Clue 2: Eric is the person whose birthday is in September
solver.add(house1_birthday == 'sept')

# Clue 3: The person who loves science fiction books is in the second house
solver.add(house2_book_genre == 'science fiction')

# Clue 4: The person who keeps horses is the person whose birthday is in September
solver.add(Or(
    And(house1_animal == 'horse', house1_birthday == 'sept'),
    And(house2_animal == 'horse', house2_birthday == 'sept')
))

# Add constraints for unique values
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_book_genre, house2_book_genre))
solver.add(Distinct(house1_birthday, house2_birthday))
solver.add(Distinct(house1_animal, house2_animal))

# Add domain constraints
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house1_book_genre == 'science fiction', house1_book_genre == 'mystery'))
solver.add(Or(house1_birthday == 'april', house1_birthday == 'sept'))
solver.add(Or(house1_animal == 'horse', house1_animal == 'cat'))

solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house2_book_genre == 'science fiction', house2_book_genre == 'mystery'))
solver.add(Or(house2_birthday == 'april', house2_birthday == 'sept'))
solver.add(Or(house2_animal == 'horse', house2_animal == 'cat'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    solution_house1 = [str(model[house1_name]), str(model[house1_book_genre]), str(model[house1_birthday]), str(model[house1_animal])]
    solution_house2 = [str(model[house2_name]), str(model[house2_book_genre]), str(model[house2_birthday]), str(model[house2_animal])]
    
    # Format the solution as JSON
    solution_json = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": [
                ["1"] + solution_house1,
                ["2"] + solution_house2
            ]
        }
    }
    
    print(solution_json)
else:
    print("No solution found")