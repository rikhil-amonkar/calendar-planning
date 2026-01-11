from z3 import *

# Define the domain for each variable (0 to 3)
domain = range(4)

# Create variables for each characteristic in each house
names = [Int(f"name_{i}") for i in domain]
cigars = [Int(f"cigar_{i}") for i in domain]
sports = [Int(f"sport_{i}") for i in domain]
drinks = [Int(f"drink_{i}") for i in domain]

# Create the solver
solver = Solver()

# Add constraints for uniqueness within each characteristic
solver.add(Distinct(names))
solver.add(Distinct(cigars))
solver.add(Distinct(sports))
solver.add(Distinct(drinks))

# Map indices to names, cigars, sports, and drinks
name_map = {0: "Alice", 1: "Peter", 2: "Arnold", 3: "Eric"}
cigar_map = {0: "prince", 1: "dunhill", 2: "blue master", 3: "pall mall"}
sport_map = {0: "swimming", 1: "basketball", 2: "soccer", 3: "tennis"}
drink_map = {0: "coffee", 1: "water", 2: "milk", 3: "tea"}

# Add constraints based on the clues
# Clue 1: Peter is in the fourth house.
solver.add(names[3] == 1)

# Clue 2: The tea drinker is the person who loves basketball.
# Since the person who loves basketball is Eric (Clue 4), Eric drinks tea.
solver.add(drinks[2] == 3)

# Clue 3: Arnold is the person who smokes Blue Master.
solver.add(cigars[2] == 2)

# Clue 4: The person who loves basketball is Eric.
solver.add(sports[2] == 1)

# Clue 5: The person who loves tennis is the person who smokes Blue Master.
# Since Arnold smokes Blue Master (Clue 3), Arnold loves tennis.
solver.add(sports[2] == 3)

# Clue 6: There are two houses between the one who only drinks water and Peter.
# Peter is in the fourth house, so the water drinker must be in the first or second house.
water_drinker = Or(drinks[0] == 1, drinks[1] == 1)
solver.add(water_drinker)

# Clue 7: The coffee drinker is Arnold.
solver.add(drinks[2] == 0)

# Clue 8: The person who loves basketball is in the third house.
# This is already handled by Clue 4.

# Clue 9: The Prince smoker is the person who loves soccer.
# Since the person who loves soccer is not specified directly, we need to find the remaining person.
# The remaining person who loves soccer is Alice (since Arnold loves tennis and Eric loves basketball).
solver.add(cigars[0] == 0)

# Clue 10: Peter is the person partial to Pall Mall.
solver.add(cigars[3] == 3)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in domain:
        name_val = name_map[model.evaluate(names[i]).as_long()]
        cigar_val = cigar_map[model.evaluate(cigars[i]).as_long()]
        sport_val = sport_map[model.evaluate(sports[i]).as_long()]
        drink_val = drink_map[model.evaluate(drinks[i]).as_long()]
        solution.append([str(i+1), name_val, cigar_val, sport_val, drink_val])
    
    # Format the solution as required
    result = {
        "solution": {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")