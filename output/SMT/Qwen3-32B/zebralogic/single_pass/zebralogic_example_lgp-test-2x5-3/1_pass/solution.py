import json
from z3 import *

# Define EnumSorts
Names, (Eric, Arnold) = EnumSort('Names', ['Eric', 'Arnold'])
Hobbies, (gardening, photography) = EnumSort('Hobbies', ['gardening', 'photography'])
BookGenres, (mystery, science_fiction) = EnumSort('BookGenres', ['mystery', 'science_fiction'])
MusicGenres, (rock, pop) = EnumSort('MusicGenres', ['rock', 'pop'])
Birthdays, (april, september) = EnumSort('Birthdays', ['april', 'september'])

# Create variables for each house
# House 1
name1 = Const('name1', Names)
hobby1 = Const('hobby1', Hobbies)
book_genre1 = Const('book_genre1', BookGenres)
music_genre1 = Const('music_genre1', MusicGenres)
birthday1 = Const('birthday1', Birthdays)

# House 2
name2 = Const('name2', Names)
hobby2 = Const('hobby2', Hobbies)
book_genre2 = Const('book_genre2', BookGenres)
music_genre2 = Const('music_genre2', MusicGenres)
birthday2 = Const('birthday2', Birthdays)

s = Solver()

# Add uniqueness constraints
s.add(name1 != name2)
s.add(hobby1 != hobby2)
s.add(book_genre1 != book_genre2)
s.add(music_genre1 != music_genre2)
s.add(birthday1 != birthday2)

# Add clue constraints
s.add(name1 == Eric)  # clue2: Arnold not in first house
s.add(name2 == Arnold)

s.add(book_genre1 == mystery)  # clue5
s.add(hobby1 == gardening)  # clue3
s.add(music_genre1 == rock)  # clue1

s.add(birthday2 == april)  # clue4: Arnold's birthday is april

# Check if satisfiable
if s.check() == sat:
    model = s.model()
    # Now extract the values for each house
    # For house 1:
    h1_name = model[name1]
    h1_hobby = model[hobby1]
    h1_book = model[book_genre1]
    h1_music = model[music_genre1]
    h1_bday = model[birthday1]

    # For house 2:
    h2_name = model[name2]
    h2_hobby = model[hobby2]
    h2_book = model[book_genre2]
    h2_music = model[music_genre2]
    h2_bday = model[birthday2]

    # Now, construct the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": [
                [
                    "1",
                    str(h1_name),
                    str(h1_hobby),
                    str(h1_book).replace('_', ' '),
                    str(h1_music),
                    str(h1_bday)
                ],
                [
                    "2",
                    str(h2_name),
                    str(h2_hobby),
                    str(h2_book).replace('_', ' '),
                    str(h2_music),
                    str(h2_bday)
                ]
            ]
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")