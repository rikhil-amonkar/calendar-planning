from z3 import *
import json

# Define the solver
solver = Solver()

# Define variables
houses = [1, 2]
names = ['Eric', 'Arnold']
hobbies = ['gardening', 'photography']
book_genres = ['science fiction', 'mystery']
music_genres = ['rock', 'pop']
birthdays = ['april', 'sept']

# Create dictionaries to hold the variables
name_vars = {house: Int(f'name_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}
book_genre_vars = {house: Int(f'book_genre_{house}') for house in houses}
music_genre_vars = {house: Int(f'music_genre_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hobby_vars[house] for house in houses]))
solver.add(Distinct([book_genre_vars[house] for house in houses]))
solver.add(Distinct([music_genre_vars[house] for house in houses]))
solver.add(Distinct([birthday_vars[house] for house in houses]))

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}
music_genre_map = {genre: i for i, genre in enumerate(music_genres)}
birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}

# Add constraints based on clues
# Clue 1: The person who loves mystery books is the person who loves rock music.
solver.add(Implies(book_genre_vars[1] == book_genre_map['mystery'], music_genre_vars[1] == music_genre_map['rock']))
solver.add(Implies(book_genre_vars[2] == book_genre_map['mystery'], music_genre_vars[2] == music_genre_map['rock']))

# Clue 2: Arnold is not in the first house.
solver.add(name_vars[1] != name_map['Arnold'])

# Clue 3: The person who loves mystery books is the person who enjoys gardening.
solver.add(Implies(book_genre_vars[1] == book_genre_map['mystery'], hobby_vars[1] == hobby_map['gardening']))
solver.add(Implies(book_genre_vars[2] == book_genre_map['mystery'], hobby_vars[2] == hobby_map['gardening']))

# Clue 4: The person whose birthday is in April is Arnold.
solver.add(Implies(birthday_vars[1] == birthday_map['april'], name_vars[1] == name_map['Arnold']))
solver.add(Implies(birthday_vars[2] == birthday_map['april'], name_vars[2] == name_map['Arnold']))

# Clue 5: The person who loves mystery books is in the first house.
solver.add(book_genre_vars[1] == book_genre_map['mystery'])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": []
        }
    }
    
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        book_genre = book_genres[model[book_genre_vars[house]].as_long()]
        music_genre = music_genres[model[music_genre_vars[house]].as_long()]
        birthday = birthdays[model[birthday_vars[house]].as_long()]
        
        solution["solution"]["rows"].append([
            str(house), name, hobby, book_genre, music_genre, birthday
        ])
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")