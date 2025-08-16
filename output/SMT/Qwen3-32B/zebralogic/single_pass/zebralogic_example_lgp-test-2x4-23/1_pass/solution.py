import z3
import json

solver = z3.Solver()

# Variables for house 1 and 2
name1 = z3.Int('name1')
name2 = z3.Int('name2')
mother1 = z3.Int('mother1')
mother2 = z3.Int('mother2')
car1 = z3.Int('car1')
car2 = z3.Int('car2')
height1 = z3.Int('height1')
height2 = z3.Int('height2')

# Uniqueness constraints
solver.add(name1 != name2)
solver.add(mother1 != mother2)
solver.add(car1 != car2)
solver.add(height1 != height2)

# All variables are 0 or 1
for var in [name1, name2, mother1, mother2, car1, car2, height1, height2]:
    solver.add(var >= 0, var <= 1)

# Clue 3: mother2 is Holly (1)
solver.add(mother2 == 1)

# Clue 2: if name is Arnold (1), height is 1 (short)
solver.add(z3.Implies(name1 == 1, height1 == 1))
solver.add(z3.Implies(name2 == 1, height2 == 1))

# Clue 1: Tesla (car == 1) is to the right of Arnold (name == 1)
solver.add(z3.Implies(name1 == 1, car2 == 1))
solver.add(z3.Implies(name2 == 1, False))  # Arnold can't be in house 2

if solver.check() == z3.sat:
    model = solver.model()
    # Extract values for house 1 and 2
    def get_value(var):
        return model[var].as_long()
    
    # House 1
    h1_name = "Eric" if get_value(name1) == 0 else "Arnold"
    h1_mother = "Aniya" if get_value(mother1) == 0 else "Holly"
    h1_car = "ford f150" if get_value(car1) == 0 else "tesla model 3"
    h1_height = "very short" if get_value(height1) == 0 else "short"
    
    # House 2
    h2_name = "Eric" if get_value(name2) == 0 else "Arnold"
    h2_mother = "Aniya" if get_value(mother2) == 0 else "Holly"
    h2_car = "ford f150" if get_value(car2) == 0 else "tesla model 3"
    h2_height = "very short" if get_value(height2) == 0 else "short"
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": [
                ["1", h1_name, h1_mother, h1_car, h1_height],
                ["2", h2_name, h2_mother, h2_car, h2_height]
            ]
        }
    }
    
    print(json.dumps(solution))
else:
    print("No solution found.")