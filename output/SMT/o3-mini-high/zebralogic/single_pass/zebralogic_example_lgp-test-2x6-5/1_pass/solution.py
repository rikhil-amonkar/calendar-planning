from z3 import Solver, Int, Or, sat
import json

# Create a Z3 solver instance
solver = Solver()

# Define integer variables for House 1 attributes
house1_name   = Int('house1_name')
house1_occ    = Int('house1_occ')
house1_bday   = Int('house1_bday')
house1_style  = Int('house1_style')
house1_height = Int('house1_height')
house1_cigar  = Int('house1_cigar')

# Define integer variables for House 2 attributes
house2_name   = Int('house2_name')
house2_occ    = Int('house2_occ')
house2_bday   = Int('house2_bday')
house2_style  = Int('house2_style')
house2_height = Int('house2_height')
house2_cigar  = Int('house2_cigar')

# All variables can only be 0 or 1.
vars = [house1_name, house1_occ, house1_bday, house1_style, house1_height, house1_cigar,
        house2_name, house2_occ, house2_bday, house2_style, house2_height, house2_cigar]
for var in vars:
    solver.add(Or(var == 0, var == 1))

# Enforce uniqueness for each attribute category between houses.
solver.add(house1_name != house2_name)
solver.add(house1_occ  != house2_occ)
solver.add(house1_bday != house2_bday)
solver.add(house1_style != house2_style)
solver.add(house1_height != house2_height)
solver.add(house1_cigar  != house2_cigar)

# Mappings for our domains:
# Names:         0 -> "Arnold",  1 -> "Eric"
# Occupations:   0 -> "engineer", 1 -> "doctor"
# Birthdays:     0 -> "april",    1 -> "sept"
# HouseStyles:   0 -> "colonial", 1 -> "victorian"
# Heights:       0 -> "very short", 1 -> "short"
# Cigars:        0 -> "prince",   1 -> "pall mall"

# Clue 1: The engineer is in the first house.
# We'll denote engineer as 0.
solver.add(house1_occ == 0)

# Clue 6: The engineer is Eric.
# Since house1 is the engineer, house1's name must be Eric (which we'll assign index 1).
solver.add(house1_name == 1)

# Clue 3: The person living in a colonial-style house is the engineer.
# So house1 (engineer) must live in a colonial house (index 0).
solver.add(house1_style == 0)

# Clue 4: The person who is very short is the engineer.
# So house1 (engineer) must be very short (index 0).
solver.add(house1_height == 0)

# Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
# With only two houses, and house1 already being engineer, this forces:
# House1 must have birthday in April (index 0) and House2 must be the doctor.
solver.add(house1_bday == 0)
solver.add(house2_occ == 1)

# Clue 5: The person who is short is partial to Pall Mall.
# Since house1 is very short (index 0), the only candidate for "short" is house2.
# This implies house2's height is 1 and thus their cigar must be Pall Mall (index 1).
solver.add(house2_height == 1)
solver.add(house2_cigar == 1)

# (The remaining values are forced by uniqueness:
# House2_name will be 0 -> "Arnold",
# House2_bday will be 1 -> "sept",
# House2_style will be 1 -> "victorian",
# and house1_cigar will be 0 -> "prince".)

# Check the model
if solver.check() == sat:
    model = solver.model()
    
    # Define our mapping dictionaries
    name_map = {0: "Arnold", 1: "Eric"}
    occ_map = {0: "engineer", 1: "doctor"}
    bday_map = {0: "april", 1: "sept"}
    style_map = {0: "colonial", 1: "victorian"}
    height_map = {0: "very short", 1: "short"}
    cigar_map = {0: "prince", 1: "pall mall"}
    
    house1 = [
        "1",
        name_map[model[house1_name].as_long()],
        occ_map[model[house1_occ].as_long()],
        bday_map[model[house1_bday].as_long()],
        style_map[model[house1_style].as_long()],
        height_map[model[house1_height].as_long()],
        cigar_map[model[house1_cigar].as_long()]
    ]
    
    house2 = [
        "2",
        name_map[model[house2_name].as_long()],
        occ_map[model[house2_occ].as_long()],
        bday_map[model[house2_bday].as_long()],
        style_map[model[house2_style].as_long()],
        height_map[model[house2_height].as_long()],
        cigar_map[model[house2_cigar].as_long()]
    ]
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": [house1, house2]
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")