from z3 import *
import json

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3]
names = ['Arnold', 'Eric', 'Peter']
music_genres = ['pop', 'rock', 'classical']
children = ['Fred', 'Meredith', 'Bella']
book_genres = ['mystery', 'romance', 'science fiction']

# Declare variables for each characteristic
name_vars = {house: Int(f'name_{house}') for house in houses}
music_genre_vars = {house: Int(f'music_genre_{house}') for house in houses}
child_vars = {house: Int(f'child_{house}') for house in houses}
book_genre_vars = {house: Int(f'book_genre_{house}') for house in houses}

# Map strings to integers for Z3
name_map = {name: i for i, name in enumerate(names)}
music_genre_map = {genre: i for i, genre in enumerate(music_genres)}
child_map = {child: i for i, child in enumerate(children)}
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([music_genre_vars[house] for house in houses]))
solver.add(Distinct([child_vars[house] for house in houses]))
solver.add(Distinct([book_genre_vars[house] for house in houses]))

# Add specific constraints based on the clues
# Clue 1: The person's child is named Fred is directly left of the person who loves mystery books.
solver.add(Implies(child_vars[1] == child_map['Fred'], book_genre_vars[2] == book_genre_map['mystery']))
solver.add(Implies(child_vars[2] == child_map['Fred'], book_genre_vars[3] == book_genre_map['mystery']))

# Clue 2: Peter is in the first house.
solver.add(name_vars[1] == name_map['Peter'])

# Clue 3: The person who loves mystery books is the person who loves classical music.
solver.add([Implies(book_genre_vars[house] == book_genre_map['mystery'], music_genre_vars[house] == music_genre_map['classical']) for house in houses])

# Clue 4: The person who loves science fiction books is the person's child is named Meredith.
solver.add([Implies(book_genre_vars[house] == book_genre_map['science fiction'], child_vars[house] == child_map['Meredith']) for house in houses])

# Clue 5: Eric is the person who loves mystery books.
solver.add([Implies(name_vars[house] == name_map['Eric'], book_genre_vars[house] == book_genre_map['mystery']) for house in houses])

# Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
solver.add(Or(
    And(book_genre_vars[1] == book_genre_map['romance'], music_genre_vars[2] == music_genre_map['rock']),
    And(book_genre_vars[1] == book_genre_map['romance'], music_genre_vars[3] == music_genre_map['rock']),
    And(book_genre_vars[2] == book_genre_map['romance'], music_genre_vars[3] == music_genre_map['rock'])
))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": []
        }
    }
    for house in houses:
        name_index = model.evaluate(name_vars[house]).as_long()
        music_genre_index = model.evaluate(music_genre_vars[house]).as_long()
        child_index = model.evaluate(child_vars[house]).as_long()
        book_genre_index = model.evaluate(book_genre_vars[house]).as_long()
        
        # Ensure the indices are within the valid range
        if 0 <= name_index < len(names) and 0 <= music_genre_index < len(music_genres) and 0 <= child_index < len(children) and 0 <= book_genre_index < len(book_genres):
            name = names[name_index]
            music_genre = music_genres[music_genre_index]
            child = children[child_index]
            book_genre = book_genres[book_genre_index]
            solution["solution"]["rows"].append([str(house), name, music_genre, child, book_genre])
        else:
            print(f"Index out of range for house {house}: name={name_index}, music_genre={music_genre_index}, child={child_index}, book_genre={book_genre_index}")
    
    print(json.dumps(solution))
else:
    print("No solution found")