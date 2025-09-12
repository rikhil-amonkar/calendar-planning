from z3 import *
import json

# Define the variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_book_genre = String('house1_book_genre')
house2_book_genre = String('house2_book_genre')
house1_vacation = String('house1_vacation')
house2_vacation = String('house2_vacation')
house1_animal = String('house1_animal')
house2_animal = String('house2_animal')
house1_music_genre = String('house1_music_genre')
house2_music_genre = String('house2_music_genre')

# Create the solver
solver = Solver()

# Define the domain for each variable
names = ['Arnold', 'Eric']
book_genres = ['science fiction', 'mystery']
vacations = ['mountain', 'beach']
animals = ['cat', 'horse']
music_genres = ['rock', 'pop']

# Add constraints for unique values within each category
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_book_genre, house2_book_genre))
solver.add(Distinct(house1_vacation, house2_vacation))
solver.add(Distinct(house1_animal, house2_animal))
solver.add(Distinct(house1_music_genre, house2_music_genre))

# Add constraints based on the clues
solver.add(house2_vacation == 'beach')  # Clue 1
solver.add(house2_music_genre == 'pop')  # Clue 2
solver.add(house1_music_genre == 'rock')  # Clue 3
solver.add(house1_book_genre == 'mystery')  # Clue 4
solver.add(house1_animal != 'cat')  # Clue 5
solver.add(house1_book_genre == 'mystery')  # Clue 6

# Define the possible values for each variable
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))
solver.add(Or(house1_book_genre == 'science fiction', house1_book_genre == 'mystery'))
solver.add(Or(house2_book_genre == 'science fiction', house2_book_genre == 'mystery'))
solver.add(Or(house1_vacation == 'mountain', house1_vacation == 'beach'))
solver.add(Or(house2_vacation == 'mountain', house2_vacation == 'beach'))
solver.add(Or(house1_animal == 'cat', house1_animal == 'horse'))
solver.add(Or(house2_animal == 'cat', house2_animal == 'horse'))
solver.add(Or(house1_music_genre == 'rock', house1_music_genre == 'pop'))
solver.add(Or(house2_music_genre == 'rock', house2_music_genre == 'pop'))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_book_genre].as_string(), model[house1_vacation].as_string(), model[house1_animal].as_string(), model[house1_music_genre].as_string()],
                ["2", model[house2_name].as_string(), model[house2_book_genre].as_string(), model[house2_vacation].as_string(), model[house2_animal].as_string(), model[house2_music_genre].as_string()]
            ]
        }
    }
    print(json.dumps(solution))
else:
    print("No solution found")