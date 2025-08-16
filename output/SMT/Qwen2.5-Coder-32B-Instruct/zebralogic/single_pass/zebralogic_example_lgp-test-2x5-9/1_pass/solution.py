from z3 import *

# Create Solver
solver = Solver()

# Define variables
names = ['Arnold', 'Eric']
book_genres = ['science fiction', 'mystery']
vacations = ['mountain', 'beach']
animals = ['cat', 'horse']
music_genres = ['rock', 'pop']

# Create symbolic variables for each attribute
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

# Add constraints for unique values
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_book_genre, house2_book_genre))
solver.add(Distinct(house1_vacation, house2_vacation))
solver.add(Distinct(house1_animal, house2_animal))
solver.add(Distinct(house1_music_genre, house2_music_genre))

# Add given clues as constraints
# Clue 1: The person who loves beach vacations is Eric.
solver.add(Or(house1_vacation == 'beach' & house1_name == 'Eric',
             house2_vacation == 'beach' & house2_name == 'Eric'))

# Clue 2: The person who loves pop music is the person who loves beach vacations.
solver.add(Or((house1_vacation == 'beach') & (house1_music_genre == 'pop'),
             (house2_vacation == 'beach') & (house2_music_genre == 'pop')))

# Clue 3: The person who loves rock music is the person who loves mystery books.
solver.add(Or((house1_music_genre == 'rock') & (house1_book_genre == 'mystery'),
             (house2_music_genre == 'rock') & (house2_book_genre == 'mystery')))

# Clue 4: The cat lover is not in the second house.
solver.add(house2_animal != 'cat')

# Clue 5: The person who loves mystery books is in the first house.
solver.add(house1_book_genre == 'mystery')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": [
                ["1",
                 model[house1_name].as_string(),
                 model[house1_book_genre].as_string(),
                 model[house1_vacation].as_string(),
                 model[house1_animal].as_string(),
                 model[house1_music_genre].as_string()],
                ["2",
                 model[house2_name].as_string(),
                 model[house2_book_genre].as_string(),
                 model[house2_vacation].as_string(),
                 model[house2_animal].as_string(),
                 model[house2_music_genre].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")