from z3 import *

# Define variables
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

# Define possible values
names = ['Arnold', 'Eric']
book_genres = ['science fiction', 'mystery']
vacations = ['mountain', 'beach']
animals = ['cat', 'horse']
music_genres = ['rock', 'pop']

# Create solver instance
solver = Solver()

# Add constraints for each variable to be one of the possible values
solver.add(house1_name == names[0] | house1_name == names[1])
solver.add(house2_name == names[0] | house2_name == names[1])
solver.add(house1_book_genre == book_genres[0] | house1_book_genre == book_genres[1])
solver.add(house2_book_genre == book_genres[0] | house2_book_genre == book_genres[1])
solver.add(house1_vacation == vacations[0] | house1_vacation == vacations[1])
solver.add(house2_vacation == vacations[0] | house2_vacation == vacations[1])
solver.add(house1_animal == animals[0] | house1_animal == animals[1])
solver.add(house2_animal == animals[0] | house2_animal == animals[1])
solver.add(house1_music_genre == music_genres[0] | house1_music_genre == music_genres[1])
solver.add(house2_music_genre == music_genres[0] | house2_music_genre == music_genres[1])

# Add uniqueness constraints
solver.add(house1_name != house2_name)
solver.add(house1_book_genre != house2_book_genre)
solver.add(house1_vacation != house2_vacation)
solver.add(house1_animal != house2_animal)
solver.add(house1_music_genre != house2_music_genre)

# Encode clues
# Clue 1: The person who loves beach vacations is Eric.
solver.add(Implies(house1_vacation == 'beach', house1_name == 'Eric'))
solver.add(Implies(house2_vacation == 'beach', house2_name == 'Eric'))

# Clue 2: The person who loves pop music is the person who loves beach vacations.
solver.add(Implies(house1_music_genre == 'pop', house1_vacation == 'beach'))
solver.add(Implies(house2_music_genre == 'pop', house2_vacation == 'beach'))

# Clue 3: The person who loves rock music is the person who loves mystery books.
solver.add(Implies(house1_music_genre == 'rock', house1_book_genre == 'mystery'))
solver.add(Implies(house2_music_genre == 'rock', house2_book_genre == 'mystery'))

# Clue 4: The cat lover is not in the second house.
solver.add(house2_animal != 'cat')

# Clue 5: The person who loves mystery books is in the first house.
solver.add(house1_book_genre == 'mystery')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    house1_solution = [
        "1",
        model[house1_name].as_string(),
        model[house1_book_genre].as_string(),
        model[house1_vacation].as_string(),
        model[house1_animal].as_string(),
        model[house1_music_genre].as_string()
    ]
    house2_solution = [
        "2",
        model[house2_name].as_string(),
        model[house2_book_genre].as_string(),
        model[house2_vacation].as_string(),
        model[house2_animal].as_string(),
        model[house2_music_genre].as_string()
    ]
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": [house1_solution, house2_solution]
        }
    }
    print(solution)
else:
    print("No solution found")