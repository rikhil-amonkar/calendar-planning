from z3 import *

# Create a solver instance
solver = Solver()

# Define the domains
houses = [1, 2, 3, 4]
names = ["Eric", "Arnold", "Peter", "Alice"]
hair_colors = ["blonde", "black", "brown", "red"]
music_genres = ["pop", "jazz", "rock", "classical"]

# Create variables
name_vars = {house: Int(f"name_{house}") for house in houses}
hair_color_vars = {house: Int(f"hair_color_{house}") for house in houses}
music_genre_vars = {house: Int(f"music_genre_{house}") for house in houses}

# Define the mappings
name_map = {name: i for i, name in enumerate(names)}
hair_color_map = {color: i for i, color in enumerate(hair_colors)}
music_genre_map = {genre: i for i, genre in enumerate(music_genres)}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))
solver.add(Distinct([music_genre_vars[house] for house in houses]))

# Add specific constraints based on the clues
# Clue 1: Eric is the person who has red hair.
for house in houses:
    solver.add(Implies(name_vars[house] == name_map["Eric"], hair_color_vars[house] == hair_color_map["red"]))

# Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
for house in range(1, 4):
    solver.add(Implies(music_genre_vars[house] == music_genre_map["classical"], hair_color_vars[house + 1] == hair_color_map["blonde"]))

# Clue 3: The person who has brown hair is not in the first house.
solver.add(hair_color_vars[1] != hair_color_map["brown"])

# Clue 4: The person who loves pop music is not in the third house.
solver.add(music_genre_vars[3] != music_genre_map["pop"])

# Clue 5: The person who loves classical music is in the first house.
solver.add(music_genre_vars[1] == music_genre_map["classical"])

# Clue 6: The person who loves jazz music is the person who has red hair.
for house in houses:
    solver.add(Implies(music_genre_vars[house] == music_genre_map["jazz"], hair_color_vars[house] == hair_color_map["red"]))

# Clue 7: The person who loves rock music is Arnold.
for house in houses:
    solver.add(Implies(music_genre_vars[house] == music_genre_map["rock"], name_vars[house] == name_map["Arnold"]))

# Clue 8: Peter is somewhere to the right of the person who loves rock music.
for house_rock in houses:
    for house_peter in range(house_rock + 1, 5):
        solver.add(Implies(music_genre_vars[house_rock] == music_genre_map["rock"], name_vars[house_peter] == name_map["Peter"]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        hair_color = hair_colors[model.evaluate(hair_color_vars[house]).as_long()]
        music_genre = music_genres[model.evaluate(music_genre_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, hair_color, music_genre])
    import json
    print(json.dumps(solution))
else:
    print("No solution found")