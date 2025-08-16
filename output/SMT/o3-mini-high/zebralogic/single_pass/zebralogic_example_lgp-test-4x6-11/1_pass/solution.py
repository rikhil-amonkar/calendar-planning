from z3 import *
import json

# Create a solver instance
solver = Solver()

# Declare integer variables for each attribute.
# Names
peter   = Int("peter")
alice   = Int("alice")
eric    = Int("eric")
arnold  = Int("arnold")

# Hobbies (use lower-case names; note: cooking, painting, gardening, photography)
cook    = Int("cook")   # cooking; Group A: also equals romance (book) and jazz (music)
paint   = Int("paint")  # painting
garden  = Int("garden") # gardening; Group D: equals Arnold and april (birthday)
photo   = Int("photo")  # photography

# Animals
fish    = Int("fish")   # fish; will equal Peter (Group B)
cat     = Int("cat")
bird    = Int("bird")
horse   = Int("horse")  # horse; will equal rock (Group C)

# Book Genres
fantasy = Int("fantasy")
mystery = Int("mystery")  # Group C: will equal rock
romance = Int("romance")  # Group A: will equal cook
scifi   = Int("scifi")

# Birthdays (months)
april   = Int("april")   # Group D: equals garden
jan     = Int("jan")
sept    = Int("sept")
feb     = Int("feb")     # Group B: will equal Peter

# Music Genres
pop       = Int("pop")       # Group B: equals Peter
rock      = Int("rock")      # Group C: equals mystery and also equals horse
classical = Int("classical")
jazz      = Int("jazz")      # Group A: equals cook

# Domain constraints: Each variable represents a house number 1..4
variables = [peter, alice, eric, arnold,
             cook, paint, garden, photo,
             fish, cat, bird, horse,
             fantasy, mystery, romance, scifi,
             april, jan, sept, feb,
             pop, rock, classical, jazz]

for var in variables:
    solver.add(var >= 1, var <= 4)

# Now add the clues as constraints:

# Clue 1: The person who loves cooking is the person who loves romance books.
solver.add(cook == romance)

# Clue 9: The person who loves jazz music is the person who loves cooking.
solver.add(jazz == cook)

# Clue 15: The person who loves cooking is not in the third house.
solver.add(cook != 3)

# Clue 2: The person whose birthday is in February is the person who loves pop music.
solver.add(feb == pop)

# Clue 5: The person whose birthday is in February is the fish enthusiast.
solver.add(feb == fish)

# Clue 12: Peter is the person who loves pop music.
solver.add(peter == pop)

# Clue 7: The person who keeps horses is the person who loves rock music.
solver.add(horse == rock)

# Clue 10: The person who loves rock music is the person who loves mystery books.
solver.add(rock == mystery)

# Clue 14: The person who loves rock music is directly left of the person whose birthday is in January.
solver.add(rock + 1 == jan)

# Clue 8: The person who enjoys gardening is the person whose birthday is in April.
solver.add(garden == april)

# Clue 13: The person who enjoys gardening is Arnold.
solver.add(arnold == garden)

# Clue 11: The person who paints as a hobby is directly left of the person who loves romance books.
# (Since romance equals cooking, we have paint immediately to the left of cook)
solver.add(paint + 1 == cook)

# Clue 3: Eric is not in the second house.
solver.add(eric != 2)

# Clue 4: The person who loves romance books is not in the fourth house.
solver.add(romance != 4)

# Clue 6: Alice is somewhere to the right of the person who loves fantasy books.
solver.add(alice > fantasy)

# Clue 16: The cat lover is somewhere to the right of the person who keeps horses.
solver.add(cat > rock)

# Additionally, from clue 15 (included above) and Clue 4 we already have cook != 3 and cook != 4 because romance == cook.

# Also impose distinctness within each category.

# Names: Peter, Alice, Eric, Arnold
solver.add(Distinct(peter, alice, eric, arnold))

# Hobbies: cooking (cook), painting (paint), gardening (garden), photography (photo)
solver.add(Distinct(cook, paint, garden, photo))

# Animals: fish, cat, bird, horse
solver.add(Distinct(fish, cat, bird, horse))

# Book Genres: fantasy, mystery, romance, science fiction (scifi)
solver.add(Distinct(fantasy, mystery, romance, scifi))

# Birthdays: april, jan, sept, feb
solver.add(Distinct(april, jan, sept, feb))

# Music: pop, rock, classical, jazz
solver.add(Distinct(pop, rock, classical, jazz))

# Solve the puzzle.
if solver.check() == sat:
    model = solver.model()

    # Build dictionaries for each category to map house numbers to the attribute string.
    # For names:
    names = {}
    if model[peter].as_long() in range(1, 5):
        names[model[peter].as_long()] = "Peter"
    if model[alice].as_long() in range(1, 5):
        names[model[alice].as_long()] = "Alice"
    if model[eric].as_long() in range(1, 5):
        names[model[eric].as_long()] = "Eric"
    if model[arnold].as_long() in range(1, 5):
        names[model[arnold].as_long()] = "Arnold"

    # Hobbies:
    hobbies = {}
    if model[cook].as_long() in range(1, 5):
        hobbies[model[cook].as_long()] = "cooking"
    if model[paint].as_long() in range(1, 5):
        hobbies[model[paint].as_long()] = "painting"
    if model[garden].as_long() in range(1, 5):
        hobbies[model[garden].as_long()] = "gardening"
    if model[photo].as_long() in range(1, 5):
        hobbies[model[photo].as_long()] = "photography"

    # Animals:
    animals = {}
    if model[fish].as_long() in range(1, 5):
        animals[model[fish].as_long()] = "fish"
    if model[cat].as_long() in range(1, 5):
        animals[model[cat].as_long()] = "cat"
    if model[bird].as_long() in range(1, 5):
        animals[model[bird].as_long()] = "bird"
    if model[horse].as_long() in range(1, 5):
        animals[model[horse].as_long()] = "horse"

    # Book Genres:
    books = {}
    if model[fantasy].as_long() in range(1, 5):
        books[model[fantasy].as_long()] = "fantasy"
    # Note: mystery is equated to rock.
    if model[rock].as_long() in range(1, 5):
        books[model[rock].as_long()] = "mystery"
    if model[romance].as_long() in range(1, 5):
        books[model[romance].as_long()] = "romance"
    if model[scifi].as_long() in range(1, 5):
        books[model[scifi].as_long()] = "science fiction"

    # Birthdays:
    birthdays = {}
    if model[april].as_long() in range(1, 5):
        birthdays[model[april].as_long()] = "april"
    if model[jan].as_long() in range(1, 5):
        birthdays[model[jan].as_long()] = "jan"
    if model[sept].as_long() in range(1, 5):
        birthdays[model[sept].as_long()] = "sept"
    if model[feb].as_long() in range(1, 5):
        birthdays[model[feb].as_long()] = "feb"

    # Music:
    music = {}
    if model[pop].as_long() in range(1, 5):
        music[model[pop].as_long()] = "pop"
    if model[rock].as_long() in range(1, 5):
        music[model[rock].as_long()] = "rock"
    if model[classical].as_long() in range(1, 5):
        music[model[classical].as_long()] = "classical"
    if model[jazz].as_long() in range(1, 5):
        music[model[jazz].as_long()] = "jazz"

    # Build a list of rows sorted by house number.
    # Each row: ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"]
    rows = []
    for house in range(1, 5):
        row = [str(house),
               names.get(house, ""),
               hobbies.get(house, ""),
               animals.get(house, ""),
               books.get(house, ""),
               birthdays.get(house, ""),
               music.get(house, "")]
        rows.append(row)

    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": rows
        }
    }
    # Print the JSON output.
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")