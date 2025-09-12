from z3 import *

# Define the variables
houses = range(1, 7)
names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
house_styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
music_genres = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

# Create dictionaries to map each attribute to a Z3 variable
name_vars = {name: Int(name) for name in names}
house_style_vars = {style: Int(style) for style in house_styles}
music_genre_vars = {genre: Int(genre) for genre in music_genres}
hobby_vars = {hobby: Int(hobby) for hobby in hobbies}

# Create a solver instance
solver = Solver()

# Add constraints for each attribute to be in the range of houses
for var_dict in [name_vars, house_style_vars, music_genre_vars, hobby_vars]:
    for var in var_dict.values():
        solver.add(And(var >= 1, var <= 6))

# Add constraints for each attribute to be unique
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(house_style_vars.values())))
solver.add(Distinct(list(music_genre_vars.values())))
solver.add(Distinct(list(hobby_vars.values())))

# Add specific clues as constraints
# Clue 1
solver.add(music_genre_vars["rock"] == 5)

# Clue 2
solver.add(
    Or(
        Abs(house_style_vars["victorian"] - music_genre_vars["classical"]) == 1,
        Abs(house_style_vars["victorian"] - hobby_vars["woodworking"]) == 1,
        Abs(music_genre_vars["classical"] - hobby_vars["woodworking"]) == 1
    )
)

# Clue 3
solver.add(music_genre_vars["hip hop"] == house_style_vars["mediterranean"])

# Clue 4
solver.add(Abs(name_vars["Arnold"] - house_style_vars["victorian"]) == 3)

# Clue 5
solver.add(music_genre_vars["jazz"] + 1 == name_vars["Eric"])

# Clue 6
solver.add(music_genre_vars["hip hop"] < hobby_vars["knitting"])

# Clue 7
solver.add(music_genre_vars["hip hop"] == name_vars["Carol"])

# Clue 8
solver.add(house_style_vars["craftsman"] == name_vars["Arnold"])

# Clue 9
solver.add(house_style_vars["ranch"] == name_vars["Eric"])

# Clue 10
solver.add(hobby_vars["woodworking"] == house_style_vars["victorian"])

# Clue 11
solver.add(music_genre_vars["country"] == 1)

# Clue 12
solver.add(
    Or(
        Abs(hobby_vars["painting"] - house_style_vars["colonial"]) == 1
    )
)

# Clue 13
solver.add(hobby_vars["photography"] == name_vars["Alice"])

# Clue 14
solver.add(hobby_vars["gardening"] == name_vars["Eric"])

# Clue 15
solver.add(name_vars["Bob"] == 3)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {"solution": {"header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"], "rows": []}}
    for house in houses:
        name = next(name for name, var in name_vars.items() if model[var] == house)
        house_style = next(style for style, var in house_style_vars.items() if model[var] == house)
        music_genre = next(genre for genre, var in music_genre_vars.items() if model[var] == house)
        hobby = next(hobby for hobby, var in hobby_vars.items() if model[var] == house)
        solution["solution"]["rows"].append([str(house), name, house_style, music_genre, hobby])
    
    import json
    print(json.dumps(solution))
else:
    print("No solution found")