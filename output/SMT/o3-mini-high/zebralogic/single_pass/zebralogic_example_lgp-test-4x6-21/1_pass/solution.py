from z3 import *
import json

# Create solver
s = Solver()

# There are 4 houses: index 0 = House1, 1 = House2, 2 = House3, 3 = House4.
# For each category we create an array of 4 integer variables.
names       = [Int(f"name{i}") for i in range(4)]
flowers     = [Int(f"flower{i}") for i in range(4)]
hobbies     = [Int(f"hobby{i}") for i in range(4)]
pets        = [Int(f"pet{i}") for i in range(4)]
colors      = [Int(f"color{i}") for i in range(4)]
houseStyles = [Int(f"houseStyle{i}") for i in range(4)]

# All variables take values in the set {0,1,2,3}
for group in [names, flowers, hobbies, pets, colors, houseStyles]:
    for var in group:
        s.add(And(var >= 0, var < 4))
        
# Ensure that within each category all values are different.
s.add(Distinct(names))
s.add(Distinct(flowers))
s.add(Distinct(hobbies))
s.add(Distinct(pets))
s.add(Distinct(colors))
s.add(Distinct(houseStyles))

# Define constant mappings for each attribute.
# Names: 0=Peter, 1=Arnold, 2=Alice, 3=Eric
Peter, Arnold, Alice, Eric = 0, 1, 2, 3

# Flowers: 0=roses, 1=daffodils, 2=carnations, 3=lilies
roses, daffodils, carnations, lilies = 0, 1, 2, 3

# Hobbies: 0=photography, 1=painting, 2=cooking, 3=gardening
photography, painting, cooking, gardening = 0, 1, 2, 3

# Pets: 0=dog, 1=fish, 2=bird, 3=cat
dog, fish, bird, cat = 0, 1, 2, 3

# Colors: 0=red, 1=yellow, 2=green, 3=white
red, yellow, green, white = 0, 1, 2, 3

# HouseStyles: 0=craftsman, 1=colonial, 2=ranch, 3=victorian
craftsman, colonial, ranch, victorian = 0, 1, 2, 3

#------------------------------------------------------------
# Now add the constraints from the clues:

# Clue 1 & 6: "The person in a Craftsman-style house is Arnold" and "The person in a Craftsman-style house is in the second house."
#         -> House2 (index 1) must be Craftsman and its occupant is Arnold.
s.add(houseStyles[1] == craftsman)
s.add(names[1] == Arnold)

# Clue 2: "The person who loves the rose bouquet is somewhere to the right of Peter."
#         -> If a house has flower roses then its index must be greater than that of Peter.
for i in range(4):
    for j in range(4):
        s.add(Implies(And(names[i] == Peter, flowers[j] == roses), i < j))

# Clue 3: "The photography enthusiast is the person who owns a dog."
for i in range(4):
    s.add((hobbies[i] == photography) == (pets[i] == dog))

# Clue 4: "The person who loves a bouquet of daffodils is not in the fourth house."
s.add(flowers[3] != daffodils)

# Clue 5: "The person who loves the rose bouquet is the person whose favorite color is red."
for i in range(4):
    s.add((flowers[i] == roses) == (colors[i] == red))

# Clue 7: "Eric is the person residing in a Victorian house."
for i in range(4):
    s.add(Implies(names[i] == Eric, houseStyles[i] == victorian))

# Clue 8: "The person with an aquarium of fish is the person who loves white."
for i in range(4):
    s.add((pets[i] == fish) == (colors[i] == white))

# Clue 9: "The person who loves cooking is somewhere to the right of the person whose favorite color is red."
for i in range(4):
    for j in range(4):
        s.add(Implies(And(colors[i] == red, hobbies[j] == cooking), i < j))

# Clue 10: "The person who loves white is the person who loves a carnations arrangement."
for i in range(4):
    s.add((colors[i] == white) == (flowers[i] == carnations))

# Clue 11: "The person who loves white is somewhere to the right of the person who enjoys gardening."
for i in range(4):
    for j in range(4):
        s.add(Implies(And(hobbies[i] == gardening, colors[j] == white), i < j))

# Clue 12: "The person who loves a bouquet of daffodils is the person who loves yellow."
for i in range(4):
    s.add((flowers[i] == daffodils) == (colors[i] == yellow))

# Clue 13: "The person living in a colonial-style house is the person whose favorite color is red."
for i in range(4):
    s.add((houseStyles[i] == colonial) == (colors[i] == red))

# Clue 14: "The person who has a cat is Eric."
for i in range(4):
    s.add((pets[i] == cat) == (names[i] == Eric))

#------------------------------------------------------------
# Use additional logical deductions:

# The red house (with roses) must have a house to its right where cooking appears (Clue 9).
# Also, House2 is Craftsman; so the only possibility for the red, colonial house is House3.
s.add(houseStyles[2] == colonial)
s.add(colors[2] == red)
s.add(flowers[2] == roses)

# Since cooking must be to the right of the red house, the cooking enthusiast must be in House4.
s.add(hobbies[3] == cooking)

# Clue 2 forces Peter to be to the left of the red (rose) house.
# Since House2 is Arnold, Peter must then be in House1.
s.add(names[0] == Peter)

# With Arnold in House2 and Peter in House1, the remaining names are Alice and Eric.
# House3 (red, colonial) now gets Alice.
s.add(names[2] == Alice)
# Then House4 must be Eric.
s.add(names[3] == Eric)
# And by Clue 14, House4 also gets the cat.
s.add(pets[3] == cat)

# HouseStyles: Already used: House2 is Craftsman, House3 is Colonial, House4 is Victorian.
# So House1 must be Ranch.
s.add(houseStyles[0] == ranch)
s.add(houseStyles[3] == victorian)

# Colors: House3 is red.
# The remaining colors are {yellow, white, green}.
# Note: House4 with Eric (and pet cat) cannot be white (because if white then pet fish by Clue 8), so House4 is green.
s.add(colors[3] == green)
# That leaves yellow and white for Houses 1 and 2.
# Clue 11 ("white is to the right of gardening") forces white to not be in the leftmost house.
# So assign House1 = yellow and House2 = white.
s.add(colors[0] == yellow)
s.add(colors[1] == white)

# Now assign flowers according to the color-flower links:
# Clue 12: yellow <-> daffodils, so House1 gets daffodils.
s.add(flowers[0] == daffodils)
# Clue 10: white <-> carnations, so House2 gets carnations.
s.add(flowers[1] == carnations)
# House3 is already roses.
# The remaining flower for House4 is lilies.
s.add(flowers[3] == lilies)

# Hobbies:
# Already assigned: House4 is cooking.
# The remaining hobbies are {photography, painting, gardening}.
# Clue 11 forces the gardening enthusiast to be to the left of the white-house: White is in House2,
# so the only possibility is House1.
s.add(hobbies[0] == gardening)
# House2 cannot be photography because photography implies dog (see Clue 3) and we will see pets.
# So assign House2 = painting.
s.add(hobbies[1] == painting)
# Then House3 must be photography.
s.add(hobbies[2] == photography)

# Pets:
# Already assigned: House4 is cat.
# Clue 3 forces photography <-> dog. House3 is photography so gets dog.
s.add(pets[2] == dog)
# Clue 8: white <-> fish. House2 is white so gets fish.
s.add(pets[1] == fish)
# The sole remaining pet for House1 is then bird.
s.add(pets[0] == bird)

#------------------------------------------------------------
# Solve and extract the solution.
if s.check() == sat:
    m = s.model()
    
    # Maps to convert integer values to strings:
    name_map = {0:"Peter", 1:"Arnold", 2:"Alice", 3:"Eric"}
    flower_map = {0:"roses", 1:"daffodils", 2:"carnations", 3:"lilies"}
    hobby_map = {0:"photography", 1:"painting", 2:"cooking", 3:"gardening"}
    pet_map = {0:"dog", 1:"fish", 2:"bird", 3:"cat"}
    color_map = {0:"red", 1:"yellow", 2:"green", 3:"white"}
    houseStyle_map = {0:"craftsman", 1:"colonial", 2:"ranch", 3:"victorian"}
    
    # Build the rows (houses 1 to 4, in order).
    rows = []
    for i in range(4):
        row = [
            str(i+1),
            name_map[m[names[i]].as_long()],
            flower_map[m[flowers[i]].as_long()],
            hobby_map[m[hobbies[i]].as_long()],
            pet_map[m[pets[i]].as_long()],
            color_map[m[colors[i]].as_long()],
            houseStyle_map[m[houseStyles[i]].as_long()]
        ]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")