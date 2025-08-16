from z3 import *

# Create Solver
solver = Solver()

# Define Variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_hobby = String('house1_hobby')
house2_hobby = String('house2_hobby')
house1_book_genre = String('house1_book_genre')
house2_book_genre = String('house2_book_genre')
house1_music_genre = String('house1_music_genre')
house2_music_genre = String('house2_music_genre')
house1_birthday = String('house1_birthday')
house2_birthday = String('house2_birthday')

# Define Domains
names = ['Eric', 'Arnold']
hobbies = ['gardening', 'photography']
book_genres = ['science fiction', 'mystery']
music_genres = ['rock', 'pop']
birthdays = ['april', 'sept']

# Constraints for domains
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Distinct(house1_name, house2_name))

solver.add(Or(house1_hobby == 'gardening', house1_hobby == 'photography'))
solver.add(Or(house2_hobby == 'gardening', house2_hobby == 'photography'))
solver.add(Distinct(house1_hobby, house2_hobby))

solver.add(Or(house1_book_genre == 'science fiction', house1_book_genre == 'mystery'))
solver.add(Or(house2_book_genre == 'science fiction', house2_book_genre == 'mystery'))
solver.add(Distinct(house1_book_genre, house2_book_genre))

solver.add(Or(house1_music_genre == 'rock', house1_music_genre == 'pop'))
solver.add(Or(house2_music_genre == 'rock', house2_music_genre == 'pop'))
solver.add(Distinct(house1_music_genre, house2_music_genre))

solver.add(Or(house1_birthday == 'april', house1_birthday == 'sept'))
solver.add(Or(house2_birthday == 'april', house2_birthday == 'sept'))
solver.add(Distinct(house1_birthday, house2_birthday))

# Clue 1: The person who loves mystery books is the person who loves rock music.
solver.add(Implies(house1_book_genre == 'mystery', house1_music_genre == 'rock'))
solver.add(Implies(house2_book_genre == 'mystery', house2_music_genre == 'rock'))

# Clue 2: Arnold is not in the first house.
solver.add(house1_name != 'Arnold')

# Clue 3: The person who loves mystery books is the person who enjoys gardening.
solver.add(Implies(house1_book_genre == 'mystery', house1_hobby == 'gardening'))
solver.add(Implies(house2_book_genre == 'mystery', house2_hobby == 'gardening'))

# Clue 4: The person whose birthday is in April is Arnold.
solver.add(house1_birthday == 'april' >> house1_name == 'Arnold')
solver.add(house2_birthday == 'april' >> house2_name == 'Arnold')

# Clue 5: The person who loves mystery books is in the first house.
solver.add(house1_book_genre == 'mystery')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": [
                ["1",
                 model[house1_name].as_string(),
                 model[house1_hobby].as_string(),
                 model[house1_book_genre].as_string(),
                 model[house1_music_genre].as_string(),
                 model[house1_birthday].as_string()],
                ["2",
                 model[house2_name].as_string(),
                 model[house2_hobby].as_string(),
                 model[house2_book_genre].as_string(),
                 model[house2_music_genre].as_string(),
                 model[house2_birthday].as_string()]
            ]
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")