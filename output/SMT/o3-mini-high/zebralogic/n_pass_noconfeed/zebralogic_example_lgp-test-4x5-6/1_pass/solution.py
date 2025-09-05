from z3 import *
import json

# Mapping constants
# Names: Peter=0, Eric=1, Alice=2, Arnold=3
Peter = 0
Eric = 1
Alice = 2
Arnold = 3

# Education: bachelor=0, high school=1, associate=2, master=3
Bachelor = 0
HighSchool = 1
Associate = 2
Master = 3

# Music: jazz=0, rock=1, pop=2, classical=3
Jazz = 0
Rock = 1
Pop = 2
Classical = 3

# Color: green=0, red=1, yellow=2, white=3
Green = 0
Red = 1
Yellow = 2
White = 3

# Flower: lilies=0, carnations=1, daffodils=2, roses=3
Lilies = 0
Carnations = 1
Daffodils = 2
Roses = 3

# Create the Z3 solver
s = Solver()

houses = 4
# Define variables: one list per attribute for each house (indexed 0 to 3 corresponding to houses 1 to 4)
names = [Int(f"name_{i}") for i in range(houses)]
edus = [Int(f"edu_{i}") for i in range(houses)]
musics = [Int(f"music_{i}") for i in range(houses)]
colors = [Int(f"color_{i}") for i in range(houses)]
flowers = [Int(f"flower_{i}") for i in range(houses)]

# Domain constraints: each variable is in the range 0..3.
for i in range(houses):
    s.add(And(names[i] >= 0, names[i] < 4))
    s.add(And(edus[i] >= 0, edus[i] < 4))
    s.add(And(musics[i] >= 0, musics[i] < 4))
    s.add(And(colors[i] >= 0, colors[i] < 4))
    s.add(And(flowers[i] >= 0, flowers[i] < 4))

# Uniqueness constraints: all houses have distinct attribute values in every category.
s.add(Distinct(names))
s.add(Distinct(edus))
s.add(Distinct(musics))
s.add(Distinct(colors))
s.add(Distinct(flowers))

# Clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
# (edu == Bachelor) <-> (flower == Daffodils)
for i in range(houses):
    s.add((edus[i] == Bachelor) == (flowers[i] == Daffodils))

# Clue 2: The person who loves a carnations arrangement is not in the first house.
s.add(flowers[0] != Carnations)

# Clue 3: The person with a master's degree is Alice.
# (edu == Master) <-> (name == Alice)
for i in range(houses):
    s.add((edus[i] == Master) == (names[i] == Alice))

# Clue 4: The person with a master's degree is directly left of the person who loves classical music.
for i in range(houses - 1):
    s.add(Implies(edus[i] == Master, musics[i+1] == Classical))
# Also, master's degree cannot be in the last house.
s.add(edus[houses - 1] != Master)

# Clue 5: Eric is not in the second house.
s.add(names[1] != Eric)

# Clue 6: Arnold is not in the third house.
s.add(names[2] != Arnold)

# Clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
for i in range(houses - 1):
    s.add(Implies(colors[i] == Yellow, flowers[i+1] == Roses))

# Clue 8: The person who loves pop music is in the second house.
s.add(musics[1] == Pop)

# Clue 9: The person with an associate's degree is not in the fourth house.
s.add(edus[houses - 1] != Associate)

# Clue 10: The person who loves a carnations arrangement is not in the fourth house.
s.add(flowers[houses - 1] != Carnations)

# Clue 11: The person whose favorite color is red is directly left of the person who loves white.
for i in range(houses - 1):
    s.add(Implies(colors[i] == Red, colors[i+1] == White))

# Clue 12: The person whose favorite color is red is the person who loves rock music.
for i in range(houses):
    s.add((colors[i] == Red) == (musics[i] == Rock))

# Clue 13: Arnold is the person who loves yellow.
for i in range(houses):
    s.add((names[i] == Arnold) == (colors[i] == Yellow))

# Clue 14: The person who loves a bouquet of daffodils is the person who loves yellow.
for i in range(houses):
    s.add((flowers[i] == Daffodils) == (colors[i] == Yellow))

# Solve the puzzle
if s.check() == sat:
    m = s.model()
    # Mapping dictionaries for converting integer values back to their string representations
    names_mapping = {Peter: "Peter", Eric: "Eric", Alice: "Alice", Arnold: "Arnold"}
    edus_mapping = {Bachelor: "bachelor", HighSchool: "high school", Associate: "associate", Master: "master"}
    music_mapping = {Jazz: "jazz", Rock: "rock", Pop: "pop", Classical: "classical"}
    color_mapping = {Green: "green", Red: "red", Yellow: "yellow", White: "white"}
    flower_mapping = {Lilies: "lilies", Carnations: "carnations", Daffodils: "daffodils", Roses: "roses"}
    
    solution_rows = []
    for i in range(houses):
        house_number = str(i + 1)
        name_val = names_mapping[m.evaluate(names[i]).as_long()]
        edu_val = edus_mapping[m.evaluate(edus[i]).as_long()]
        music_val = music_mapping[m.evaluate(musics[i]).as_long()]
        color_val = color_mapping[m.evaluate(colors[i]).as_long()]
        flower_val = flower_mapping[m.evaluate(flowers[i]).as_long()]
        solution_rows.append([house_number, name_val, edu_val, music_val, color_val, flower_val])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output))
else:
    print(json.dumps({"solution": None}))