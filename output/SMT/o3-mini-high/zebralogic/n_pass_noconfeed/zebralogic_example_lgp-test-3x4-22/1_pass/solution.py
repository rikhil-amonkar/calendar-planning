from z3 import *
import json

# Create solver
s = Solver()

# There are 3 houses. We'll represent each house's attributes as Z3 Int variables.
num_houses = 3

# For each house, we have four attributes: Name, MusicGenre, Children, BookGenre.
# We'll convert each attribute to an integer in the domain {0, 1, 2} with the following mapping:
# Names: 0 -> "Arnold", 1 -> "Eric", 2 -> "Peter"
# MusicGenre: 0 -> "pop", 1 -> "rock", 2 -> "classical"
# Children: 0 -> "Fred", 1 -> "Meredith", 2 -> "Bella"
# BookGenre: 0 -> "mystery", 1 -> "romance", 2 -> "science fiction"

names = [Int(f"name_{i}") for i in range(num_houses)]
musics = [Int(f"music_{i}") for i in range(num_houses)]
children = [Int(f"child_{i}") for i in range(num_houses)]
books = [Int(f"book_{i}") for i in range(num_houses)]

# Define domain constraints for each attribute in each house (each in {0,1,2})
for i in range(num_houses):
    s.add(And(names[i] >= 0, names[i] < 3))
    s.add(And(musics[i] >= 0, musics[i] < 3))
    s.add(And(children[i] >= 0, children[i] < 3))
    s.add(And(books[i] >= 0, books[i] < 3))

# All attributes are distinct across houses in their categories.
s.add(Distinct(names))
s.add(Distinct(musics))
s.add(Distinct(children))
s.add(Distinct(books))

# Mappings for final output:
names_map = ["Arnold", "Eric", "Peter"]
music_map = ["pop", "rock", "classical"]
children_map = ["Fred", "Meredith", "Bella"]
book_map = ["mystery", "romance", "science fiction"]

# Clue 2: "Peter is in the first house."
# House numbering: index 0 is the first house (leftmost).
s.add(names[0] == 2)  # 2 corresponds to "Peter"

# Clue 1: "The person's child is named Fred is directly left of the person who loves mystery books."
# Interpretation: The house whose child is Fred (child==0) must be immediately to the left of a house whose book genre is mystery (book==0).
# Since there is exactly one Fred and mystery, we constrain:
# Either house0 has Fred and house1 has mystery OR house1 has Fred and house2 has mystery.
s.add(Or(And(children[0] == 0, books[1] == 0),
         And(children[1] == 0, books[2] == 0)))
# Also, Fred cannot be in the rightmost house because then no house is to its right.
s.add(children[2] != 0)

# Clue 3: "The person who loves mystery books is the person who loves classical music."
# That is, for each house, book mystery (0) if and only if music classical (2).
for i in range(num_houses):
    s.add(books[i] == 0 if musics[i] == 2 else True)
    s.add(musics[i] == 2 if books[i] == 0 else True)
    # Alternatively, using equivalence:
    s.add(Implies(books[i] == 0, musics[i] == 2))
    s.add(Implies(musics[i] == 2, books[i] == 0))

# Clue 4: "The person who loves science fiction books is the person's child is named Meredith."
# Interpretation: The house whose child is Meredith (child==1) must be the same house
# as the one that loves science fiction (book==2). So for each house:
for i in range(num_houses):
    s.add(Implies(children[i] == 1, books[i] == 2))
    s.add(Implies(books[i] == 2, children[i] == 1))

# Clue 5: "Eric is the person who loves mystery books."
# For each house, if the name is Eric (1) then the book must be mystery (0).
for i in range(num_houses):
    s.add(Implies(names[i] == 1, books[i] == 0))

# Clue 6: "The person who loves rock music is somewhere to the right of the person who loves romance books."
# Since each attribute is unique, there is exactly one house with romance (book==1)
# and one house with rock music (music==1). We enforce that the position (index) of the house with rock
# is greater than the position of the house with romance.
pos_romance = Sum([If(books[i] == 1, i, 0) for i in range(num_houses)])
pos_rock = Sum([If(musics[i] == 1, i, 0) for i in range(num_houses)])
s.add(pos_rock > pos_romance)

# Check for a solution
if s.check() == sat:
    m = s.model()
    # Prepare the solution rows in order of houses 1, 2, 3 (indices 0,1,2)
    solution_rows = []
    for i in range(num_houses):
        house_num = str(i + 1)
        name_value = names_map[m[names[i]].as_long()]
        music_value = music_map[m[musics[i]].as_long()]
        child_value = children_map[m[children[i]].as_long()]
        book_value = book_map[m[books[i]].as_long()]
        solution_rows.append([house_num, name_value, music_value, child_value, book_value])
    
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution_dict, indent=2))
else:
    print(json.dumps({"solution": None}))