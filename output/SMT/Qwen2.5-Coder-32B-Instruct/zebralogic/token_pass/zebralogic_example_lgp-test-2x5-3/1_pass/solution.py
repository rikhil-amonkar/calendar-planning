from z3 import *

# Define variables for each attribute for both houses
name1, name2 = Ints('name1 name2')
hobby1, hobby2 = Ints('hobby1 hobby2')
book_genre1, book_genre2 = Ints('book_genre1 book_genre2')
music_genre1, music_genre2 = Ints('music_genre1 music_genre2')
birthday1, birthday2 = Ints('birthday1 birthday2')

# Define domains for each variable
names = {'Eric': 0, 'Arnold': 1}
hobbies = {'gardening': 0, 'photography': 1}
book_genres = {'science fiction': 0, 'mystery': 1}
music_genres = {'rock': 0, 'pop': 1}
birthdays = {'april': 0, 'sept': 1}

# Create solver instance
solver = Solver()

# Add constraints based on the clues
# Clue 1: The person who loves mystery books is the person who loves rock music.
solver.add(Or(book_genre1 != book_genres['mystery'], music_genre1 == music_genres['rock']))
solver.add(Or(book_genre2 != book_genres['mystery'], music_genre2 == music_genres['rock']))

# Clue 2: Arnold is not in the first house.
solver.add(name1 != names['Arnold'])

# Clue 3: The person who loves mystery books is the person who enjoys gardening.
solver.add(Or(book_genre1 != book_genres['mystery'], hobby1 == hobbies['gardening']))
solver.add(Or(book_genre2 != book_genres['mystery'], hobby2 == hobbies['gardening']))

# Clue 4: The person whose birthday is in April is Arnold.
solver.add(Or(birthday1 != birthdays['april'], name1 == names['Arnold']))
solver.add(Or(birthday2 != birthdays['april'], name2 == names['Arnold']))

# Clue 5: The person who loves mystery books is in the first house.
solver.add(book_genre1 == book_genres['mystery'])

# Ensure names are unique
solver.add(name1 != name2)

# Ensure hobbies are unique
solver.add(hobby1 != hobby2)

# Ensure book genres are unique
solver.add(book_genre1 != book_genre2)

# Ensure music genres are unique
solver.add(music_genre1 != music_genre2)

# Ensure birthdays are unique
solver.add(birthday1 != birthday2)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    # Map the model values back to the original domain
    def get_value(var, mapping):
        return [k for k, v in mapping.items() if model[var] == v][0]
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": [
                ["1", get_value(name1, names), get_value(hobby1, hobbies), get_value(book_genre1, book_genres), get_value(music_genre1, music_genres), get_value(birthday1, birthdays)],
                ["2", get_value(name2, names), get_value(hobby2, hobbies), get_value(book_genre2, book_genres), get_value(music_genre2, music_genres), get_value(birthday2, birthdays)]
            ]
        }
    }
    
    print(solution)
else:
    print("No solution found")