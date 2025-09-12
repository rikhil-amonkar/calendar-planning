import z3
import json

# Define EnumSorts for each category
Name, name_consts = z3.EnumSort('Name', ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob'])
HouseStyle, housestyle_consts = z3.EnumSort('HouseStyle', ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian'])
MusicGenre, musicgenre_consts = z3.EnumSort('MusicGenre', ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock'])
Hobby, hobby_consts = z3.EnumSort('Hobby', ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting'])

# Create arrays for each attribute
name_array = z3.Array('name_array', z3.IntSort(), Name)
house_style_array = z3.Array('house_style_array', z3.IntSort(), HouseStyle)
music_genre_array = z3.Array('music_genre_array', z3.IntSort(), MusicGenre)
hobby_array = z3.Array('hobby_array', z3.IntSort(), Hobby)

s = z3.Solver()

# Add distinctness constraints for each attribute
names_list = [z3.Select(name_array, h) for h in range(1, 7)]
s.add(z3.Distinct(names_list))

house_styles_list = [z3.Select(house_style_array, h) for h in range(1, 7)]
s.add(z3.Distinct(house_styles_list))

music_genres_list = [z3.Select(music_genre_array, h) for h in range(1, 7)]
s.add(z3.Distinct(music_genres_list))

hobbies_list = [z3.Select(hobby_array, h) for h in range(1, 7)]
s.add(z3.Distinct(hobbies_list))

# Integer variables for positions
arnold_pos = z3.Int('arnold_pos')
victorian_pos = z3.Int('victorian_pos')
hiphop_pos = z3.Int('hiphop_pos')
knitting_pos = z3.Int('knitting_pos')
eric_pos = z3.Int('eric_pos')

# Clue 1: Rock music in house 5
s.add(z3.Select(music_genre_array, 5) == musicgenre_consts[5])

# Clue 2: Classical and woodworking next to each other
clue2 = z3.Or([z3.Or(
    z3.And(z3.Select(music_genre_array, i) == musicgenre_consts[4], z3.Select(hobby_array, i+1) == hobby_consts[3]),
    z3.And(z3.Select(hobby_array, i) == hobby_consts[3], z3.Select(music_genre_array, i+1) == musicgenre_consts[4])
) for i in range(1, 6)])
s.add(clue2)

# Clue 3: Mediterranean implies hip hop
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(house_style_array, h) == housestyle_consts[0], z3.Select(music_genre_array, h) == musicgenre_consts[1]))

# Clue 4: Arnold and Victorian are 3 apart
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(name_array, h) == name_consts[2], arnold_pos == h))
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(house_style_array, h) == housestyle_consts[5], victorian_pos == h))
s.add(z3.Abs(arnold_pos - victorian_pos) == 3)

# Clue 5: Jazz is directly left of Eric
clue5 = z3.Or([z3.And(z3.Select(music_genre_array, i) == musicgenre_consts[3], z3.Select(name_array, i+1) == name_consts[0]) for i in range(1, 6)])
s.add(clue5)

# Clue 6: Hip hop is left of knitting
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(music_genre_array, h) == musicgenre_consts[1], hiphop_pos == h))
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(hobby_array, h) == hobby_consts[5], knitting_pos == h))
s.add(hiphop_pos < knitting_pos)

# Clue 7: Carol's music is hip hop
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(name_array, h) == name_consts[3], z3.Select(music_genre_array, h) == musicgenre_consts[1]))

# Clue 8: Arnold's house is Craftsman
s.add(z3.Select(house_style_array, arnold_pos) == housestyle_consts[2])

# Clue 9: Eric's house is Ranch
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(name_array, h) == name_consts[0], eric_pos == h))
s.add(z3.Select(house_style_array, eric_pos) == housestyle_consts[3])

# Clue 10: Woodworking in Victorian
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(hobby_array, h) == hobby_consts[3], z3.Select(house_style_array, h) == housestyle_consts[5]))

# Clue 11: Country in house 1
s.add(z3.Select(music_genre_array, 1) == musicgenre_consts[0])

# Clue 12: One house between painting and colonial
clue12 = z3.Or([z3.Or(
    z3.And(z3.Select(hobby_array, i) == hobby_consts[1], z3.Select(house_style_array, i+2) == housestyle_consts[4]),
    z3.And(z3.Select(house_style_array, i) == housestyle_consts[4], z3.Select(hobby_array, i+2) == hobby_consts[1])
) for i in range(1, 5)])
s.add(clue12)

# Clue 13: Alice's hobby is photography
for h in range(1, 7):
    s.add(z3.Implies(z3.Select(name_array, h) == name_consts[1], z3.Select(hobby_array, h) == hobby_consts[2]))

# Clue 14: Eric's hobby is gardening
s.add(z3.Select(hobby_array, eric_pos) == hobby_consts[4])

# Clue 15: Bob is in house 3
s.add(z3.Select(name_array, 3) == name_consts[5])

# Check if the constraints are satisfiable
if s.check() == z3.sat:
    model = s.model()
    # Extract the solution
    solution = []
    for h in range(1, 7):
        name = model.eval(z3.Select(name_array, h)).as_string()
        house_style = model.eval(z3.Select(house_style_array, h)).as_string()
        music_genre = model.eval(z3.Select(music_genre_array, h)).as_string()
        hobby = model.eval(z3.Select(hobby_array, h)).as_string()
        solution.append([str(h), name, house_style, music_genre, hobby])
    # Format as JSON
    json_output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")