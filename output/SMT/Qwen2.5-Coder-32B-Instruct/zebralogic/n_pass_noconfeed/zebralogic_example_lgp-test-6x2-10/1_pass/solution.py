from z3 import *

# Define the variables
names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
music_genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']
houses = range(1, 7)

# Create dictionaries to map names and music genres to their respective variables
name_vars = {name: Int(name) for name in names}
music_genre_vars = {genre: Int(genre) for genre in music_genres}

# Create a solver instance
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct([name_vars[name] for name in names]))
solver.add(Distinct([music_genre_vars[genre] for genre in music_genres]))

# Add constraints for house numbers
for var in list(name_vars.values()) + list(music_genre_vars.values()):
    solver.add(var >= 1)
    solver.add(var <= 6)

# Apply the clues
# 1. Bob is directly left of the person who loves jazz music.
solver.add(name_vars['Bob'] + 1 == music_genre_vars['jazz'])

# 2. Eric is somewhere to the left of the person who loves hip-hop music.
solver.add(name_vars['Eric'] < music_genre_vars['hip hop'])

# 3. Carol is in the sixth house.
solver.add(name_vars['Carol'] == 6)

# 4. Eric and the person who loves hip-hop music are next to each other.
solver.add(Or(name_vars['Eric'] + 1 == music_genre_vars['hip hop'], name_vars['Eric'] - 1 == music_genre_vars['hip hop']))

# 5. The person who loves country music is Carol.
solver.add(music_genre_vars['country'] == 6)

# 6. Arnold is not in the fifth house.
solver.add(name_vars['Arnold'] != 5)

# 7. Arnold is somewhere to the right of the person who loves pop music.
solver.add(name_vars['Arnold'] > music_genre_vars['pop'])

# 8. The person who loves pop music is Peter.
solver.add(music_genre_vars['pop'] == name_vars['Peter'])

# 9. The person who loves hip-hop music is in the third house.
solver.add(music_genre_vars['hip hop'] == 3)

# 10. There is one house between Peter and Bob.
solver.add(Or(name_vars['Peter'] - name_vars['Bob'] == 2, name_vars['Bob'] - name_vars['Peter'] == 2))

# 11. The person who loves rock music is not in the fifth house.
solver.add(music_genre_vars['rock'] != 5)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": []
        }
    }
    # Create a mapping from house number to name and music genre
    house_to_name = {model.evaluate(name_vars[name]).as_long(): name for name in names}
    house_to_music_genre = {model.evaluate(music_genre_vars[genre]).as_long(): genre for genre in music_genres}
    # Populate the rows
    for house in houses:
        name = house_to_name[house]
        music_genre = house_to_music_genre[house]
        solution["solution"]["rows"].append([str(house), name, music_genre])
    # Output the solution as JSON
    import json
    print(json.dumps(solution))
else:
    print("No solution found")