from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Eric', 'Arnold', 'Peter', 'Alice']
hair_colors = ['blonde', 'black', 'brown', 'red']
music_genres = ['pop', 'jazz', 'rock', 'classical']

# Create symbolic variables for each attribute
house_names = [String(f'house_name_{i}') for i in range(1, 5)]
house_hair_colors = [String(f'house_hair_color_{i}') for i in range(1, 5)]
house_music_genres = [String(f'house_music_genre_{i}') for i in range(1, 5)]

# Add constraints for unique values
solver.add(Distinct(house_names))
solver.add(Distinct(house_hair_colors))
solver.add(Distinct(house_music_genres))

# Add constraints based on clues
# Clue 1: Eric is the person who has red hair.
solver.add(Or(
    And(house_names[0] == 'Eric', house_hair_colors[0] == 'red'),
    And(house_names[1] == 'Eric', house_hair_colors[1] == 'red'),
    And(house_names[2] == 'Eric', house_hair_colors[2] == 'red'),
    And(house_names[3] == 'Eric', house_hair_colors[3] == 'red')
))

# Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
solver.add(Or(
    And(house_music_genres[0] == 'classical', house_hair_colors[1] == 'blonde'),
    And(house_music_genres[1] == 'classical', house_hair_colors[2] == 'blonde'),
    And(house_music_genres[2] == 'classical', house_hair_colors[3] == 'blonde')
))

# Clue 3: The person who has brown hair is not in the first house.
solver.add(house_hair_colors[0] != 'brown')

# Clue 4: The person who loves pop music is not in the third house.
solver.add(house_music_genres[2] != 'pop')

# Clue 5: The person who loves classical music is in the first house.
solver.add(house_music_genres[0] == 'classical')

# Clue 6: The person who loves jazz music is the person who has red hair.
solver.add(Or(
    And(house_music_genres[0] == 'jazz', house_hair_colors[0] == 'red'),
    And(house_music_genres[1] == 'jazz', house_hair_colors[1] == 'red'),
    And(house_music_genres[2] == 'jazz', house_hair_colors[2] == 'red'),
    And(house_music_genres[3] == 'jazz', house_hair_colors[3] == 'red')
))

# Clue 7: The person who loves rock music is Arnold.
solver.add(Or(
    And(house_music_genres[0] == 'rock', house_names[0] == 'Arnold'),
    And(house_music_genres[1] == 'rock', house_names[1] == 'Arnold'),
    And(house_music_genres[2] == 'rock', house_names[2] == 'Arnold'),
    And(house_music_genres[3] == 'rock', house_names[3] == 'Arnold')
))

# Clue 8: Peter is somewhere to the right of the person who loves rock music.
solver.add(Or(
    And(house_music_genres[0] == 'rock', Or(house_names[1] == 'Peter', house_names[2] == 'Peter', house_names[3] == 'Peter')),
    And(house_music_genres[1] == 'rock', Or(house_names[2] == 'Peter', house_names[3] == 'Peter')),
    And(house_music_genres[2] == 'rock', house_names[3] == 'Peter')
))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        house_number = str(i + 1)
        name = model[house_names[i]].as_string()[1:-1]  # Remove quotes
        hair_color = model[house_hair_colors[i]].as_string()[1:-1]  # Remove quotes
        music_genre = model[house_music_genres[i]].as_string()[1:-1]  # Remove quotes
        solution.append([house_number, name, hair_color, music_genre])
    
    print({
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": solution
        }
    })
else:
    print("No solution found")