from z3 import *

# Create variables
names = ['Eric', 'Arnold', 'Peter']
smoothies = ['desert', 'watermelon', 'cherry']
book_genres = ['science fiction', 'romance', 'mystery']

# Define the variables for each house
house1_name = String('house1_name')
house2_name = String('house2_name')
house3_name = String('house3_name')

house1_smoothie = String('house1_smoothie')
house2_smoothie = String('house2_smoothie')
house3_smoothie = String('house3_smoothie')

house1_book_genre = String('house1_book_genre')
house2_book_genre = String('house2_book_genre')
house3_book_genre = String('house3_book_genre')

# Create the solver
solver = Solver()

# Add constraints for unique names, smoothies, and book genres
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_smoothie, house2_smoothie, house3_smoothie))
solver.add(Distinct(house1_book_genre, house2_book_genre, house3_book_genre))

# Add constraints based on the clues
# Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
solver.add(Or(
    And(house1_smoothie == 'cherry', house2_book_genre == 'mystery'),
    And(house1_smoothie == 'cherry', house3_book_genre == 'mystery'),
    And(house2_smoothie == 'cherry', house3_book_genre == 'mystery')
))

# Clue 2: Arnold is the person who loves mystery books.
solver.add(house1_book_genre != 'mystery')
solver.add(house2_book_genre != 'mystery')
solver.add(house3_book_genre == 'mystery')

# Clue 3: The person who loves science fiction books is not in the first house.
solver.add(house1_book_genre != 'science fiction')

# Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
solver.add(Or(
    And(house1_smoothie == 'desert', house2_book_genre == 'mystery'),
    And(house2_smoothie == 'desert', house3_book_genre == 'mystery')
))

# Clue 5: Peter is in the first house.
solver.add(house1_name == 'Peter')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_smoothie].as_string(), model[house1_book_genre].as_string()],
                ["2", model[house2_name].as_string(), model[house2_smoothie].as_string(), model[house2_book_genre].as_string()],
                ["3", model[house3_name].as_string(), model[house3_smoothie].as_string(), model[house3_book_genre].as_string()]
            ]
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")