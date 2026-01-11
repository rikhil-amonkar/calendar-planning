from z3 import *

# Define the domains for each variable
houses = range(1, 7)
names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
house_styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
music_genres = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

# Create dictionaries to map variables to their respective domains
name_vars = {house: Int(f"name_{house}") for house in houses}
style_vars = {house: Int(f"style_{house}") for house in houses}
music_vars = {house: Int(f"music_{house}") for house in houses}
hobby_vars = {house: Int(f"hobby_{house}") for house in houses}

# Create the solver
solver = Solver()

# Add domain constraints
for house in houses:
    solver.add(name_vars[house] >= 0, name_vars[house] <= len(names) - 1)
    solver.add(style_vars[house] >= 0, style_vars[house] <= len(house_styles) - 1)
    solver.add(music_vars[house] >= 0, music_vars[house] <= len(music_genres) - 1)
    solver.add(hobby_vars[house] >= 0, hobby_vars[house] <= len(hobbies) - 1)

# Add uniqueness constraints
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([style_vars[house] for house in houses]))
solver.add(Distinct([music_vars[house] for house in houses]))
solver.add(Distinct([hobby_vars[house] for house in houses]))

# Add specific constraints based on clues
# Clue 1: The person who loves rock music is in the fifth house.
solver.add(music_vars[5] == music_genres.index("rock"))

# Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
classical_music_var = Int('classical_music_var')
woodworking_hobby_var = Int('woodworking_hobby_var')
solver.add(classical_music_var >= 0, classical_music_var <= len(houses) - 1)
solver.add(woodworking_hobby_var >= 0, woodworking_hobby_var <= len(houses) - 1)
solver.add(music_vars[classical_music_var] == music_genres.index("classical"))
solver.add(hobby_vars[woodworking_hobby_var] == hobbies.index("woodworking"))
solver.add(Or(Abs(classical_music_var - woodworking_hobby_var) == 1))

# Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
solver.add(And(style_vars[house] == house_styles.index("mediterranean"), music_vars[house] == music_genres.index("hip hop")) for house in houses)

# Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
arnold_house_var = Int('arnold_house_var')
victorian_house_var = Int('victorian_house_var')
solver.add(arnold_house_var >= 0, arnold_house_var <= len(houses) - 1)
solver.add(victorian_house_var >= 0, victorian_house_var <= len(houses) - 1)
solver.add(name_vars[arnold_house_var] == names.index("Arnold"))
solver.add(style_vars[victorian_house_var] == house_styles.index("victorian"))
solver.add(Abs(arnold_house_var - victorian_house_var) == 3)

# Clue 5: The person who loves jazz music is directly left of Eric.
jazz_music_var = Int('jazz_music_var')
eric_house_var = Int('eric_house_var')
solver.add(jazz_music_var >= 0, jazz_music_var <= len(houses) - 1)
solver.add(eric_house_var >= 0, eric_house_var <= len(houses) - 1)
solver.add(music_vars[jazz_music_var] == music_genres.index("jazz"))
solver.add(name_vars[eric_house_var] == names.index("Eric"))
solver.add(jazz_music_var + 1 == eric_house_var)

# Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
hip_hop_music_var = Int('hip_hop_music_var')
knitting_hobby_var = Int('knitting_hobby_var')
solver.add(hip_hop_music_var >= 0, hip_hop_music_var <= len(houses) - 1)
solver.add(knitting_hobby_var >= 0, knitting_hobby_var <= len(houses) - 1)
solver.add(music_vars[hip_hop_music_var] == music_genres.index("hip hop"))
solver.add(hobby_vars[knitting_hobby_var] == hobbies.index("knitting"))
solver.add(hip_hop_music_var < knitting_hobby_var)

# Clue 7: Carol is the person who loves hip-hop music.
solver.add(And(name_vars[house] == names.index("Carol"), music_vars[house] == music_genres.index("hip hop")) for house in houses)

# Clue 8: The person in a Craftsman-style house is Arnold.
solver.add(And(style_vars[house] == house_styles.index("craftsman"), name_vars[house] == names.index("Arnold")) for house in houses)

# Clue 9: The person in a ranch-style home is Eric.
solver.add(And(style_vars[house] == house_styles.index("ranch"), name_vars[house] == names.index("Eric")) for house in houses)

# Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
solver.add(And(hobby_vars[house] == hobbies.index("woodworking"), style_vars[house] == house_styles.index("victorian")) for house in houses)

# Clue 11: The person who loves country music is in the first house.
solver.add(music_vars[1] == music_genres.index("country"))

# Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
painting_hobby_var = Int('painting_hobby_var')
colonial_house_var = Int('colonial_house_var')
solver.add(painting_hobby_var >= 0, painting_hobby_var <= len(houses) - 1)
solver.add(colonial_house_var >= 0, colonial_house_var <= len(houses) - 1)
solver.add(hobby_vars[painting_hobby_var] == hobbies.index("painting"))
solver.add(style_vars[colonial_house_var] == house_styles.index("colonial"))
solver.add(Abs(painting_hobby_var - colonial_house_var) == 2)

# Clue 13: Alice is the photography enthusiast.
solver.add(And(name_vars[house] == names.index("Alice"), hobby_vars[house] == hobbies.index("photography")) for house in houses)

# Clue 14: The person who enjoys gardening is Eric.
solver.add(And(hobby_vars[house] == hobbies.index("gardening"), name_vars[house] == names.index("Eric")) for house in houses)

# Clue 15: Bob is in the third house.
solver.add(name_vars[3] == names.index("Bob"))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        style = house_styles[model.evaluate(style_vars[house]).as_long()]
        music = music_genres[model.evaluate(music_vars[house]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[house]).as_long()]
        solution.append([str(house), name, style, music, hobby])
    
    print({
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": solution
        }
    })
else:
    print("No solution found")