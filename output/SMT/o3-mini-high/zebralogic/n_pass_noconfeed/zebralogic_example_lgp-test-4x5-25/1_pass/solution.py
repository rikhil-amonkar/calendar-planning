from z3 import *
import json

# Create solver instance
s = Solver()

# There are 4 houses (indexed 0 to 3 corresponding to houses 1 to 4)
num_houses = 4

# Define domain: 0..3 for each attribute.
# Mappings:
# Names: 0: "Arnold", 1: "Peter", 2: "Eric", 3: "Alice"
# HouseStyle: 0: "craftsman", 1: "colonial", 2: "victorian", 3: "ranch"
# HairColor: 0: "red", 1: "blonde", 2: "black", 3: "brown"
# Children: 0: "Bella", 1: "Fred", 2: "Meredith", 3: "Samantha"
# BookGenre: 0: "mystery", 1: "fantasy", 2: "romance", 3: "science fiction"

# Create list of IntVars for each attribute, one per house.
names_vars = [Int(f"name_{i}") for i in range(num_houses)]
styles_vars = [Int(f"style_{i}") for i in range(num_houses)]
hairs_vars = [Int(f"hair_{i}") for i in range(num_houses)]
children_vars = [Int(f"child_{i}") for i in range(num_houses)]
books_vars = [Int(f"book_{i}") for i in range(num_houses)]

# Domain constraints: Each variable is in 0..3.
for arr in [names_vars, styles_vars, hairs_vars, children_vars, books_vars]:
    for var in arr:
        s.add(var >= 0, var < num_houses)

# Each attribute in a category is assigned uniquely.
s.add(Distinct(names_vars))
s.add(Distinct(styles_vars))
s.add(Distinct(hairs_vars))
s.add(Distinct(children_vars))
s.add(Distinct(books_vars))

# Clue 1: The person in a Craftsman-style house is in the third house.
# Craftsman is coded as 0. House 3 is index 2.
s.add(styles_vars[2] == 0)

# Clue 3: The person who has brown hair is in the fourth house.
# Brown hair is coded as 3. House 4 is index 3.
s.add(hairs_vars[3] == 3)

# Clue 4: The person whose child is named Samantha is in the fourth house.
# Samantha is coded as 3. House 4 is index 3.
s.add(children_vars[3] == 3)

# Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
# Ranch is coded as 3; Red hair is coded as 0.
# Compute house numbers (1-indexed) for the unique house with red hair and ranch style.
red_house = Sum([If(hairs_vars[i] == 0, i+1, 0) for i in range(num_houses)])
ranch_house = Sum([If(styles_vars[i] == 3, i+1, 0) for i in range(num_houses)])
s.add(red_house < ranch_house)

# Clue 9: The person who has black hair is in the second house.
# Black hair is coded as 2. House 2 is index 1.
s.add(hairs_vars[1] == 2)

# Define clues that depend on the person's name and other attributes.
for i in range(num_houses):
    # Clue 2: Alice is the person who loves romance books.
    # Alice is coded as 3 in names_vars and romance is coded as 2 in books_vars.
    s.add(Implies(names_vars[i] == 3, books_vars[i] == 2))
    
    # Clue 6: Peter is the person whose child is named Bella.
    # Peter is coded as 1; Bella is coded as 0.
    s.add(Implies(names_vars[i] == 1, children_vars[i] == 0))
    
    # Clue 7: Arnold is the person who has red hair.
    # Arnold is coded as 0 and red hair as 0.
    s.add(Implies(names_vars[i] == 0, hairs_vars[i] == 0))
    
    # Clue 8: Alice is the person living in a colonial-style house.
    # Colonial is coded as 1.
    s.add(Implies(names_vars[i] == 3, styles_vars[i] == 1))
    
    # Clue 10: The person who loves fantasy books is Peter.
    # Fantasy is coded as 1.
    s.add(Implies(names_vars[i] == 1, books_vars[i] == 1))
    
    # Clue 11: Arnold is the person whose child is named Meredith.
    # Meredith is coded as 2.
    s.add(Implies(names_vars[i] == 0, children_vars[i] == 2))
    
    # Clue 13: The person who loves science fiction books is Arnold.
    # Science fiction is coded as 3.
    s.add(Implies(names_vars[i] == 0, books_vars[i] == 3))
    
    # Clue 12: The person who has black hair is Eric.
    # Eric is coded as 2.
    s.add(Implies(hairs_vars[i] == 2, names_vars[i] == 2))

# Solve the puzzle.
if s.check() == sat:
    m = s.model()
    
    # Mappings from codes to strings.
    names_map = {0: "Arnold", 1: "Peter", 2: "Eric", 3: "Alice"}
    styles_map = {0: "craftsman", 1: "colonial", 2: "victorian", 3: "ranch"}
    hairs_map = {0: "red", 1: "blonde", 2: "black", 3: "brown"}
    children_map = {0: "Bella", 1: "Fred", 2: "Meredith", 3: "Samantha"}
    books_map = {0: "mystery", 1: "fantasy", 2: "romance", 3: "science fiction"}
    
    # Build the solution rows in order of houses 1 to 4.
    rows = []
    for i in range(num_houses):
        house_number = str(i+1)
        name_val = m[names_vars[i]].as_long()
        style_val = m[styles_vars[i]].as_long()
        hair_val = m[hairs_vars[i]].as_long()
        child_val = m[children_vars[i]].as_long()
        book_val = m[books_vars[i]].as_long()
        
        row = [
            house_number,
            names_map[name_val],
            styles_map[style_val],
            hairs_map[hair_val],
            children_map[child_val],
            books_map[book_val]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": rows
        }
    }
    
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"solution": "No solution found"}))