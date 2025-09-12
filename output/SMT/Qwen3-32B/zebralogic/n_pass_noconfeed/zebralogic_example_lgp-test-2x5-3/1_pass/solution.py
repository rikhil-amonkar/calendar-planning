import z3
import json

solver = z3.Solver()

# Variables for house 1
name_1 = z3.String('name_1')
hobby_1 = z3.String('hobby_1')
book_genre_1 = z3.String('book_genre_1')
music_genre_1 = z3.String('music_genre_1')
birthday_1 = z3.String('birthday_1')

# Variables for house 2
name_2 = z3.String('name_2')
hobby_2 = z3.String('hobby_2')
book_genre_2 = z3.String('book_genre_2')
music_genre_2 = z3.String('music_genre_2')
birthday_2 = z3.String('birthday_2')

# Add constraints for possible values and uniqueness

# Names
solver.add(z3.Or(name_1 == 'Eric', name_1 == 'Arnold'))
solver.add(z3.Or(name_2 == 'Eric', name_2 == 'Arnold'))
solver.add(name_1 != name_2)

# Hobbies
solver.add(z3.Or(hobby_1 == 'gardening', hobby_1 == 'photography'))
solver.add(z3.Or(hobby_2 == 'gardening', hobby_2 == 'photography'))
solver.add(hobby_1 != hobby_2)

# Book genres
solver.add(z3.Or(book_genre_1 == 'science fiction', book_genre_1 == 'mystery'))
solver.add(z3.Or(book_genre_2 == 'science fiction', book_genre_2 == 'mystery'))
solver.add(book_genre_1 != book_genre_2)

# Music genres
solver.add(z3.Or(music_genre_1 == 'rock', music_genre_1 == 'pop'))
solver.add(z3.Or(music_genre_2 == 'rock', music_genre_2 == 'pop'))
solver.add(music_genre_1 != music_genre_2)

# Birthdays
solver.add(z3.Or(birthday_1 == 'april', birthday_1 == 'sept'))
solver.add(z3.Or(birthday_2 == 'april', birthday_2 == 'sept'))
solver.add(birthday_1 != birthday_2)

# Add the puzzle clues as constraints

# Clue 1: The person who loves mystery books is the person who loves rock music
solver.add(z3.Or(
    z3.And(book_genre_1 == 'mystery', music_genre_1 == 'rock'),
    z3.And(book_genre_2 == 'mystery', music_genre_2 == 'rock')
))

# Clue 2: Arnold is not in the first house
solver.add(name_1 != 'Arnold')

# Clue 3: The person who loves mystery books is the person who enjoys gardening
solver.add(z3.Or(
    z3.And(book_genre_1 == 'mystery', hobby_1 == 'gardening'),
    z3.And(book_genre_2 == 'mystery', hobby_2 == 'gardening')
))

# Clue 4: The person whose birthday is in April is Arnold
solver.add(z3.And(name_2 == 'Arnold', birthday_2 == 'april'))

# Clue 5: The person who loves mystery books is in the first house
solver.add(book_genre_1 == 'mystery')

if solver.check() == z3.sat:
    model = solver.model()
    
    # Extract values for house 1
    h1_name = model.eval(name_1).as_string()
    h1_hobby = model.eval(hobby_1).as_string()
    h1_book = model.eval(book_genre_1).as_string()
    h1_music = model.eval(music_genre_1).as_string()
    h1_bday = model.eval(birthday_1).as_string()
    
    # Extract values for house 2
    h2_name = model.eval(name_2).as_string()
    h2_hobby = model.eval(hobby_2).as_string()
    h2_book = model.eval(book_genre_2).as_string()
    h2_music = model.eval(music_genre_2).as_string()
    h2_bday = model.eval(birthday_2).as_string()
    
    # Create the solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": [
                ["1", h1_name, h1_hobby, h1_book, h1_music, h1_bday],
                ["2", h2_name, h2_hobby, h2_book, h2_music, h2_bday]
            ]
        }
    }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))