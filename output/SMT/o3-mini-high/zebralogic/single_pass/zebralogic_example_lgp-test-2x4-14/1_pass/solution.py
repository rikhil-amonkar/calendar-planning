from z3 import Solver, Int, Distinct, Or, sat
import json

# Create Z3 variables for each attribute.
# Domain: House numbers 1 and 2.
Arnold = Int("Arnold")
Eric = Int("Eric")

Victorian = Int("Victorian")
Colonial = Int("Colonial")

Cherry = Int("Cherry")
Desert = Int("Desert")

Dog = Int("Dog")
Cat = Int("Cat")

# Create a solver instance.
s = Solver()

# All variables can only be assigned to house 1 or 2.
for var in [Arnold, Eric, Victorian, Colonial, Cherry, Desert, Dog, Cat]:
    s.add(Or(var == 1, var == 2))

# In each category the attributes must be assigned to different houses.
s.add(Distinct(Arnold, Eric))
s.add(Distinct(Victorian, Colonial))
s.add(Distinct(Cherry, Desert))
s.add(Distinct(Dog, Cat))

# Clue 1:
# The person who likes Cherry smoothies is the person who owns a dog.
s.add(Cherry == Dog)

# Clue 2:
# The person residing in a Victorian house is the person who owns a dog.
s.add(Victorian == Dog)

# Clue 3:
# The person residing in a Victorian house is somewhere to the left of Eric.
s.add(Victorian < Eric)

# Check for a solution.
if s.check() == sat:
    m = s.model()

    # Helper function to get the house number assigned to a variable.
    def get_house(var):
        return m[var].as_long()

    # We have two houses: 1 and 2.
    houses = [1, 2]
    solution_rows = []

    for house in houses:
        # Determine the Name for the current house.
        if get_house(Arnold) == house:
            name = "Arnold"
        elif get_house(Eric) == house:
            name = "Eric"
        else:
            name = "Unknown"

        # Determine the HouseStyle for the current house.
        if get_house(Victorian) == house:
            style = "victorian"
        elif get_house(Colonial) == house:
            style = "colonial"
        else:
            style = "Unknown"

        # Determine the Smoothie for the current house.
        if get_house(Cherry) == house:
            smoothie = "cherry"
        elif get_house(Desert) == house:
            smoothie = "desert"
        else:
            smoothie = "Unknown"

        # Determine the Pet for the current house.
        if get_house(Dog) == house:
            pet = "dog"
        elif get_house(Cat) == house:
            pet = "cat"
        else:
            pet = "Unknown"

        solution_rows.append([str(house), name, style, smoothie, pet])
    
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": solution_rows
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")