from z3 import *
import json

# Create a Z3 solver instance
solver = Solver()

# Define variables. Each variable represents the house number (1 or 2) where the attribute is located.
Arnold = Int('Arnold')
Eric = Int('Eric')
Basketball = Int('Basketball')
Soccer = Int('Soccer')
Brown = Int('Brown')
Black = Int('Black')
VeryShort = Int('VeryShort')
Short = Int('Short')
Desert = Int('Desert')
Cherry = Int('Cherry')
Daffodils = Int('Daffodils')
Carnations = Int('Carnations')

# All variables have domain {1, 2}
vars_list = [Arnold, Eric, Basketball, Soccer, Brown, Black, VeryShort, Short, Desert, Cherry, Daffodils, Carnations]
for var in vars_list:
    solver.add(Or(var == 1, var == 2))

# Each category must assign different houses to the two possibilities.
solver.add(Arnold != Eric)           # Names
solver.add(Basketball != Soccer)       # FavoriteSport
solver.add(Brown != Black)             # HairColor
solver.add(VeryShort != Short)         # Height
solver.add(Desert != Cherry)           # Smoothie
solver.add(Daffodils != Carnations)    # Flower

# Clue 1: The person who loves soccer is not in the second house.
solver.add(Soccer != 2)

# Clue 2: The Desert smoothie lover is directly left of the person who is very short.
# With 2 houses (numbered 1 and 2 left-to-right), this means:
# Desert is in house 1 and VeryShort is in house 2.
solver.add(VeryShort == Desert + 1)

# Clue 3: The person who is very short is the person who has brown hair.
solver.add(VeryShort == Brown)

# Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
solver.add(Carnations == Desert)

# Clue 5: Eric and the person who has brown hair are next to each other.
solver.add(Abs(Eric - Brown) == 1)

# Solve the puzzle
if solver.check() == sat:
    model = solver.model()
    
    # Prepare a dictionary for each house (by number) to collect attributes.
    houses = {1: {}, 2: {}}
    
    # Assign Names
    for var, name in [(Arnold, "Arnold"), (Eric, "Eric")]:
        house_number = model.evaluate(var).as_long()
        houses[house_number]["Name"] = name

    # Assign FavoriteSport
    for var, sport in [(Basketball, "basketball"), (Soccer, "soccer")]:
        house_number = model.evaluate(var).as_long()
        houses[house_number]["FavoriteSport"] = sport
    
    # Assign HairColor
    for var, hair in [(Brown, "brown"), (Black, "black")]:
        house_number = model.evaluate(var).as_long()
        houses[house_number]["HairColor"] = hair
    
    # Assign Height
    for var, height in [(VeryShort, "very short"), (Short, "short")]:
        house_number = model.evaluate(var).as_long()
        houses[house_number]["Height"] = height
    
    # Assign Smoothie
    for var, smoothie in [(Desert, "desert"), (Cherry, "cherry")]:
        house_number = model.evaluate(var).as_long()
        houses[house_number]["Smoothie"] = smoothie
    
    # Assign Flower
    for var, flower in [(Daffodils, "daffodils"), (Carnations, "carnations")]:
        house_number = model.evaluate(var).as_long()
        houses[house_number]["Flower"] = flower
    
    # Construct the solution table with rows in order: house 1, then house 2.
    rows = []
    for i in [1, 2]:
        row = [
            str(i),
            houses[i].get("Name"),
            houses[i].get("FavoriteSport"),
            houses[i].get("HairColor"),
            houses[i].get("Height"),
            houses[i].get("Smoothie"),
            houses[i].get("Flower")
        ]
        rows.append(row)
    
    result = {
      "solution": {
        "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
        "rows": rows
      }
    }
    
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")