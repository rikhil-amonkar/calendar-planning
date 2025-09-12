from z3 import *
import json

solver = Solver()

# Name variables
peter = Int('peter')
arnold = Int('arnold')
eric = Int('eric')
carol = Int('carol')
alice = Int('alice')
bob = Int('bob')

# Cigar variables
blends = Int('blends')
yellow_monster = Int('yellow_monster')
pall_mall = Int('pall_mall')
blue_master = Int('blue_master')
dunhill = Int('dunhill')
prince = Int('prince')

# All variables between 1 and 6
for var in [peter, arnold, eric, carol, alice, bob, blends, yellow_monster, pall_mall, blue_master, dunhill, prince]:
    solver.add(And(1 <= var, var <= 6))

# All names distinct
solver.add(Distinct(peter, arnold, eric, carol, alice, bob))

# All cigars distinct
solver.add(Distinct(blends, yellow_monster, pall_mall, blue_master, dunhill, prince))

# Clue 2: Blue Master is in 5
solver.add(blue_master == 5)

# Clue 5: Pall Mall is in 3
solver.add(pall_mall == 3)

# Clue 6: Eric is in 6
solver.add(eric == 6)

# Clue 8: Peter is in 1
solver.add(peter == 1)

# Clue 9: Bob is in 3
solver.add(bob == 3)

# Clue 7: Carol and Eric are next to each other → Carol is in 5
solver.add(carol == 5)

# Clue 1: Arnold is left of blends
solver.add(arnold < blends)

# Clue 3: Arnold is left of prince
solver.add(arnold < prince)

# Clue 4: |yellow_monster - blends| == 2
solver.add(Or(yellow_monster - blends == 2, blends - yellow_monster == 2))

if solver.check() == sat:
    model = solver.model()
    
    # Prepare name and cigar mappings
    name_vars = [
        (peter, "Peter"),
        (arnold, "Arnold"),
        (eric, "Eric"),
        (carol, "Carol"),
        (alice, "Alice"),
        (bob, "Bob"),
    ]
    
    cigar_vars = [
        (blends, "blends"),
        (yellow_monster, "yellow monster"),
        (pall_mall, "pall mall"),
        (blue_master, "blue master"),
        (dunhill, "dunhill"),
        (prince, "prince"),
    ]
    
    rows = []
    for house_num in range(1, 7):
        # Find name
        name = None
        for var, name_str in name_vars:
            if model[var].as_long() == house_num:
                name = name_str
                break
        # Find cigar
        cigar = None
        for var, cigar_str in cigar_vars:
            if model[var].as_long() == house_num:
                cigar = cigar_str
                break
        rows.append([str(house_num), name, cigar])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")