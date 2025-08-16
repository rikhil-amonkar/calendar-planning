from z3 import Solver, Int, And, Distinct, Abs
import json

# Create a solver instance
solver = Solver()

# For mothers we create one Int variable per name.
# The value of each variable represents the house number (1 to 5) where that mother lives.
Eric    = Int("Eric")
Alice   = Int("Alice")
Peter   = Int("Peter")
Bob     = Int("Bob")
Arnold  = Int("Arnold")

# For children we create one Int variable per child.
# The value of each variable represents the house number (1 to 5) where that child is.
Timothy   = Int("Timothy")
Meredith  = Int("Meredith")
Samantha  = Int("Samantha")
Fred      = Int("Fred")
Bella     = Int("Bella")

# Domain constraints: each value is between 1 and 5.
solver.add(And(Eric  >= 1, Eric  <= 5,
               Alice >= 1, Alice <= 5,
               Peter >= 1, Peter <= 5,
               Bob   >= 1, Bob   <= 5,
               Arnold>= 1, Arnold<= 5))

solver.add(And(Timothy   >= 1, Timothy   <= 5,
               Meredith  >= 1, Meredith  <= 5,
               Samantha  >= 1, Samantha  <= 5,
               Fred      >= 1, Fred      <= 5,
               Bella     >= 1, Bella     <= 5))

# Each house gets a unique mother and a unique child.
solver.add(Distinct(Eric, Alice, Peter, Bob, Arnold))
solver.add(Distinct(Timothy, Meredith, Samantha, Fred, Bella))

# Now add the clues.
# Clue 1: Bob is somewhere to the left of the house where the child is Samantha.
solver.add(Bob < Samantha)

# Clue 2: The person who is the mother of Timothy is (in the house where Timothy is)
# somewhere to the left of the house where the child is Samantha.
# (Since every mother is with her child, the house where Timothy appears is that mother's house.)
solver.add(Timothy < Samantha)

# Clue 3: The house whose child is named Fred is the second house.
solver.add(Fred == 2)

# Clue 7: The house whose child is named Fred is directly left of the house whose child is Bella.
solver.add(Bella == Fred + 1)

# Clue 4: There is one house between Alice and the house where the child is Samantha.
solver.add(Abs(Alice - Samantha) == 2)

# Clue 5: Eric is not in the third house.
solver.add(Eric != 3)

# Clue 6: Bob is not in the third house.
solver.add(Bob != 3)

# Clue 8: The house where the child is Samantha is somewhere to the left of the house where Peter is.
solver.add(Samantha < Peter)

# Solve the constraints.
if solver.check() == 0:
    print("No solution found")
else:
    model = solver.model()
    
    # Build inverse maps: house number -> mother's name and house number -> child's name.
    mothers = {"Eric": model[Eric].as_long(),
               "Alice": model[Alice].as_long(),
               "Peter": model[Peter].as_long(),
               "Bob": model[Bob].as_long(),
               "Arnold": model[Arnold].as_long()}
    
    children = {"Timothy": model[Timothy].as_long(),
                "Meredith": model[Meredith].as_long(),
                "Samantha": model[Samantha].as_long(),
                "Fred": model[Fred].as_long(),
                "Bella": model[Bella].as_long()}
    
    # Invert the dictionaries: for each house number (1 to 5), find which mother and child reside there.
    house_to_mother = {}
    for mother, pos in mothers.items():
        house_to_mother[pos] = mother

    house_to_child = {}
    for child, pos in children.items():
        house_to_child[pos] = child

    # Build rows for houses 1 to 5.
    rows = []
    for house in range(1, 6):
        rows.append([str(house), house_to_mother[house], house_to_child[house]])
    
    # Build the final JSON structure.
    solution = {
      "solution": {
        "header": ["House", "Name", "Children"],
        "rows": rows
      }
    }
    
    # Print the JSON result.
    print(json.dumps(solution, indent=2))