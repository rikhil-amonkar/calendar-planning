from z3 import *

# There are 6 houses, indexed 0..5 (house number i = index+1)
# Each house has four attributes:
#   name, houseStyle, musicGenre, hobby
# All attributes are represented as an integer in {0,..,5} whose meaning is given by the following lists:

names_list   = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
styles_list  = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
music_list   = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
hobby_list   = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

# Meaning of each number:
# For Names:
#   0: Eric, 1: Alice, 2: Arnold, 3: Carol, 4: Peter, 5: Bob
# For HouseStyles:
#   0: mediterranean, 1: modern, 2: craftsman, 3: ranch, 4: colonial, 5: victorian
# For MusicGenres:
#   0: country, 1: hip hop, 2: pop, 3: jazz, 4: classical, 5: rock
# For Hobbies:
#   0: cooking, 1: painting, 2: photography, 3: woodworking, 4: gardening, 5: knitting

s = Solver()

# Create variables for each house and each attribute
houses = 6
name  = [Int(f"name_{i}") for i in range(houses)]
style = [Int(f"style_{i}") for i in range(houses)]
music = [Int(f"music_{i}") for i in range(houses)]
hobby = [Int(f"hobby_{i}") for i in range(houses)]

# Domain constraints: each variable is in 0..5
for i in range(houses):
    s.add(And(name[i] >= 0, name[i] < 6))
    s.add(And(style[i] >= 0, style[i] < 6))
    s.add(And(music[i] >= 0, music[i] < 6))
    s.add(And(hobby[i] >= 0, hobby[i] < 6))

# All attributes are all-different by category.
s.add(Distinct(name))
s.add(Distinct(style))
s.add(Distinct(music))
s.add(Distinct(hobby))

#--------------------------------------------------------------------------
# Clues:
# 1. The person who loves rock music is in the fifth house.
# (House5 is index 4)
s.add(music[4] == 5)  # rock is 5

# 11. The person who loves country music is in the first house.
s.add(music[0] == 0)  # country is 0

# 15. Bob is in the third house.
# Bob's index in names_list is 5 and third house means index 2.
s.add(name[2] == 5)

# For the “jazz left of Eric” rule later we must ensure Eric is not in the first house.
# (Because there is no house to the left in that case.)
s.add(name[0] != 0)  # Eric (0) is not in house 1

#--------------------------------------------------------------------------
# Now add the linking constraints from the clues:

# Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
# That is: style == mediterranean (0) if and only if music == hip hop (1)
for i in range(houses):
    s.add(Implies(style[i] == 0, music[i] == 1))
    s.add(Implies(music[i] == 1, style[i] == 0))

# Clue 7: Carol is the person who loves hip-hop music.
# In our names mapping, Carol is index 3.
for i in range(houses):
    s.add(Implies(name[i] == 3, music[i] == 1))
    s.add(Implies(music[i] == 1, name[i] == 3))

# Clue 8: The person in a Craftsman-style house is Arnold.
# Craftsman is style index 2; Arnold is name index 2.
for i in range(houses):
    s.add(Implies(name[i] == 2, style[i] == 2))
    s.add(Implies(style[i] == 2, name[i] == 2))

# Clue 9: The person in a Ranch-style home is Eric.
# Ranch is style index 3; Eric is name index 0.
for i in range(houses):
    s.add(Implies(name[i] == 0, style[i] == 3))
    s.add(Implies(style[i] == 3, name[i] == 0))

# Clue 13: Alice is the photography enthusiast.
# Alice is name index 1; photography is hobby index 2.
for i in range(houses):
    s.add(Implies(name[i] == 1, hobby[i] == 2))
    s.add(Implies(hobby[i] == 2, name[i] == 1))

# Clue 14: The person who enjoys gardening is Eric.
# Gardening is hobby index 4; Eric is name index 0.
for i in range(houses):
    s.add(Implies(name[i] == 0, hobby[i] == 4))
    s.add(Implies(hobby[i] == 4, name[i] == 0))

# Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
# Woodworking is hobby index 3 and Victorian is style index 5.
for i in range(houses):
    s.add(Implies(style[i] == 5, hobby[i] == 3))
    s.add(Implies(hobby[i] == 3, style[i] == 5))

#--------------------------------------------------------------------------
# Positional / relative clue constraints

# Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
# In other words, if Arnold is in position i, then a house with style == victorian (5)
# must be at i-3 or i+3 (if valid).
for i in range(houses):
    conds = []
    if i - 3 >= 0:
        conds.append(style[i-3] == 5)
    if i + 3 < houses:
        conds.append(style[i+3] == 5)
    if conds:
        s.add(Implies(name[i] == 2, Or(conds)))

# Clue 5: The person who loves jazz music is directly left of Eric.
# "Directly left" means that for any house i (0<=i<5), if the house to the right (i+1) is Eric,
# then house i must have jazz (music index 3).
for i in range(houses - 1):
    s.add(Implies(name[i+1] == 0, music[i] == 3))

# Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
# (Hip-hop is music 1; knitting is hobby 5)
for i in range(houses):
    for j in range(houses):
        s.add(Implies(And(music[i] == 1, hobby[j] == 5), i < j))

# Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
# (Painting is hobby index 1; Colonial is style index 4).
for i in range(houses):
    for j in range(houses):
        s.add(Implies(And(hobby[i] == 1, style[j] == 4), Or(j - i == 2, i - j == 2)))

# Clue 2: The person who loves classical music is next to the woodworking hobbyist.
# (Classical is music index 4; Woodworking is hobby index 3, and note clue 10 ties woodworking to Victorian.)
for i in range(houses):
    # if house i has classical music, then a neighbor must have hobby woodworking (3)
    s.add(Implies(music[i] == 4, 
                  Or(And(i > 0, hobby[i-1] == 3), And(i < houses - 1, hobby[i+1] == 3))))

#--------------------------------------------------------------------------
# (Clue 15, Clues 1 & 11 already added above)

#--------------------------------------------------------------------------
# Check and extract the solution
if s.check() == sat:
    m = s.model()
    # Build the solution table in the required JSON format.
    rows = []
    for i in range(houses):
        house_number = str(i+1)
        # convert each attribute from the model to its corresponding string
        name_str  = names_list[m.evaluate(name[i]).as_long()]
        style_str = styles_list[m.evaluate(style[i]).as_long()]
        music_str = music_list[m.evaluate(music[i]).as_long()]
        hobby_str = hobby_list[m.evaluate(hobby[i]).as_long()]
        rows.append([house_number, name_str, style_str, music_str, hobby_str])
        
    import json
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")