from z3 import *
import json

# Create a Z3 solver instance
s = Solver()

# Define house positions for each person as integer variables (allowed values: 1, 2, or 3)
Arnold = Int('Arnold')
Peter = Int('Peter')
Eric = Int('Eric')

# All persons must occupy a house between 1 and 3
s.add(And(Arnold >= 1, Arnold <= 3))
s.add(And(Peter >= 1, Peter <= 3))
s.add(And(Eric >= 1, Eric <= 3))

# No two persons can share the same house
s.add(Distinct(Arnold, Peter, Eric))

# Clue 1: Peter is somewhere to the right of Eric (i.e. his house number is greater than Eric's)
s.add(Peter > Eric)

# For the heights we have three categories: "short", "average", "very short".
# We know from Clue 2 that the person who is short is in the first house.
short_house = 1

# Introduce a variable for the house of the person who is very short.
very_short_house = Int('very_short_house')
s.add(Or(very_short_house == 1, very_short_house == 2, very_short_house == 3))

# Clue 3: There is exactly one house between the person who is short and the person who is very short.
# Since the short person is in house 1 (from Clue 2), the house for very short must differ by 2.
s.add(Abs(short_house - very_short_house) == 2)

# The remaining height "average" will be in the house that is neither short nor very short.
# (We can determine it by elimination later.)

# Clue 4: Arnold and the person who is very short are next to each other.
s.add(Abs(Arnold - very_short_house) == 1)

# Check for a solution
if s.check() == sat:
    m = s.model()
    # Determine the house number for each person from the model
    house_person = {
        m[Arnold].as_long(): "Arnold",
        m[Peter].as_long(): "Peter",
        m[Eric].as_long(): "Eric"
    }
    
    # For the heights, we know the assignments from our constraints:
    # - House 1 is "short"  (Clue 2)
    # - The house that is two apart from House 1 must be "very short" (Clue 3)
    #   Since House 1 is short, the only possibility is that House 3 is very short.
    # - The remaining house (House 2) must then have height "average".
    house_height = {
        1: "short",
        2: "average",
        3: "very short"
    }
    
    # Prepare the output rows in house order 1, 2, 3.
    rows = []
    for i in [1, 2, 3]:
        # Each row is a list: [House number as string, Name, Height]
        rows.append([str(i), house_person[i], house_height[i]])
    
    # Build the final JSON dictionary with the exact required structure.
    output = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    
    # Print the JSON-formatted solution.
    print(json.dumps(output))
else:
    print("No solution found")