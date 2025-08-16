from z3 import *
import json

# We use the following mappings:
# Names: 0 -> "Eric", 1 -> "Arnold", 2 -> "Peter", 3 -> "Alice"
# Hair Colors: 0 -> "blonde", 1 -> "black", 2 -> "brown", 3 -> "red"
# Music Genres: 0 -> "pop", 1 -> "jazz", 2 -> "rock", 3 -> "classical"

# There are 4 houses, indexed 0..3 corresponding to Houses 1..4.
num_houses = 4

# Create Z3 integer variables for each house's Name, HairColor, and MusicGenre.
names  = [Int(f"name{i}") for i in range(num_houses)]
hairs  = [Int(f"hair{i}") for i in range(num_houses)]
musics = [Int(f"music{i}") for i in range(num_houses)]

s = Solver()

# Domain constraints: each variable is in the set {0, 1, 2, 3}.
for var in names + hairs + musics:
    s.add(var >= 0, var <= 3)

# All houses must have distinct names, distinct hair colors, and distinct music genres.
s.add(Distinct(names))
s.add(Distinct(hairs))
s.add(Distinct(musics))

# Clue 5: The person who loves classical music is in the first house.
# In our mapping, "classical" is 3.
s.add(musics[0] == 3)

# Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
# Since classical is in house1 (index 0), house2 (index 1) must have blonde hair.
# In our mapping, blonde is 0.
s.add(hairs[1] == 0)

# Clue 3: The person who has brown hair is not in the first house.
# (brown = 2). (House1's hair will be set later to a value that is not 2.)
s.add(hairs[0] != 2)

# Clue 4: The person who loves pop music is not in the third house.
# (pop = 0). House3 is index 2.
s.add(musics[2] != 0)

# For each house, add the constraint that if the house's name is Eric, then his hair must be red
# and he must love jazz music.
# Clue 1: Eric has red hair. (red = 3)
# Clue 6: The person who loves jazz is the person who has red hair.
# So we impose that for a given house, name == Eric (0) <-> (hair == red (3) and music == jazz (1)).
for i in range(num_houses):
    s.add(Implies(names[i] == 0, And(hairs[i] == 3, musics[i] == 1)))
    s.add(Implies(hairs[i] == 3, names[i] == 0))
    s.add(Implies(musics[i] == 1, hairs[i] == 3))

# Clue 7: The person who loves rock music is Arnold.
# In our mapping, Arnold is 1 and rock is 2, so for each house:
for i in range(num_houses):
    s.add(Implies(names[i] == 1, musics[i] == 2))
    s.add(Implies(musics[i] == 2, names[i] == 1))

# Clue 8: Peter is somewhere to the right of the person who loves rock music (which is Arnold).
# Because there is exactly one Arnold and one Peter and houses are in order from left (house1) to right (house4),
# we enforce that if a house (with index i) has Arnold, then one of the houses to its right has Peter.
# Also, Arnold cannot be in the last house.
s.add(names[3] != 1)  # House4 cannot be Arnold.
s.add(Implies(names[0] == 1, Or(names[1] == 2, names[2] == 2, names[3] == 2)))
s.add(Implies(names[1] == 1, Or(names[2] == 2, names[3] == 2)))
s.add(Implies(names[2] == 1, names[3] == 2))

# Clue 5 already fixed House1's music to classical (3). From Clue 2, the classical-music house is immediately left of
# the blonde-haired house. Since classical is in house1, house2 must be blonde (0). This has been set.
# Also, note that since red (3) is already used for Eric and Arab (blonde 0) is used, the remaining hair colors for House1
# must be considered. House1 cannot be red (because then name would be Eric and music would have to be jazz, contradicting
# its set value classical) and cannot be blonde (because House2 is blonde). Also it cannot be brown (Clue 3). Thus, House1's hair
# must be black.
s.add(hairs[0] == 1)  # black

# At this point, most constraints will force a unique solution.
if s.check() == sat:
    m = s.model()
    
    # Define reverse mappings:
    name_map = {0: "Eric", 1: "Arnold", 2: "Peter", 3: "Alice"}
    hair_map = {0: "blonde", 1: "black", 2: "brown", 3: "red"}
    music_map = {0: "pop", 1: "jazz", 2: "rock", 3: "classical"}
    
    rows = []
    # Houses: index 0 -> House "1", index 1 -> House "2", etc.
    for i in range(num_houses):
        house_num = str(i+1)
        person = name_map[m.evaluate(names[i]).as_long()]
        hair_color = hair_map[m.evaluate(hairs[i]).as_long()]
        genre = music_map[m.evaluate(musics[i]).as_long()]
        rows.append([house_num, person, hair_color, genre])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": rows
        }
    }
    
    # Output the solution as JSON.
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")