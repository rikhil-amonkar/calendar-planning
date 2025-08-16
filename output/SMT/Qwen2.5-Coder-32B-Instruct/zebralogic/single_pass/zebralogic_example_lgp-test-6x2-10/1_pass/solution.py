from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
music_genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']

# Create dictionaries to map names and music genres to integer variables
name_vars = {name: Int(f'{name}') for name in names}
music_genre_vars = {genre: Int(f'{genre}') for genre in music_genres}

# Add constraints for each variable to be in the range [1, 6]
for var in list(name_vars.values()) + list(music_genre_vars.values()):
    solver.add(And(var >= 1, var <= 6))

# All names and music genres must be unique
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(music_genre_vars.values())))

# Apply the clues
# Clue 1: Bob is directly left of the person who loves jazz music.
solver.add(name_vars['Bob'] + 1 == music_genre_vars['jazz'])

# Clue 2: Eric is somewhere to the left of the person who loves hip-hop music.
solver.add(name_vars['Eric'] < music_genre_vars['hip hop'])

# Clue 3: Carol is in the sixth house.
solver.add(name_vars['Carol'] == 6)

# Clue 4: Eric and the person who loves hip-hop music are next to each other.
solver.add(Or(name_vars['Eric'] + 1 == music_genre_vars['hip hop'], name_vars['Eric'] - 1 == music_genre_vars['hip hop']))

# Clue 5: The person who loves country music is Carol.
solver.add(music_genre_vars['country'] == 6)

# Clue 6: Arnold is not in the fifth house.
solver.add(name_vars['Arnold'] != 5)

# Clue 7: Arnold is somewhere to the right of the person who loves pop music.
solver.add(name_vars['Arnold'] > music_genre_vars['pop'])

# Clue 8: The person who loves pop music is Peter.
solver.add(music_genre_vars['pop'] == name_vars['Peter'])

# Clue 9: The person who loves hip-hop music is in the third house.
solver.add(music_genre_vars['hip hop'] == 3)

# Clue 10: There is one house between Peter and Bob.
solver.add(Or(name_vars['Peter'] - name_vars['Bob'] == 2, name_vars['Bob'] - name_vars['Peter'] == 2))

# Clue 11: The person who loves rock music is not in the fifth house.
solver.add(music_genre_vars['rock'] != 5)

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {"solution": {"header": ["House", "Name", "MusicGenre"], "rows": []}}
    house_to_name = {model.evaluate(name_vars[name]).as_long(): name for name in names}
    house_to_music_genre = {model.evaluate(music_genre_vars[genre]).as_long(): genre for genre in music_genres}
    
    for house in range(1, 7):
        name = house_to_name[house]
        music_genre = house_to_music_genre[house]
        solution["solution"]["rows"].append([str(house), name, music_genre])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")