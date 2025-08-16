from z3 import *
import json

# Create Z3 Int variables for each attribute.
# Each variable represents the house number (1 or 2) that gets the attribute.
Eric = Int("Eric")
Arnold = Int("Arnold")
photography = Int("photography")
gardening = Int("gardening")
cat = Int("cat")
dog = Int("dog")
very_short = Int("very_short")
short = Int("short")

solver = Solver()

# Domain constraints: each variable must be either 1 or 2.
variables = [Eric, Arnold, photography, gardening, cat, dog, very_short, short]
for var in variables:
    solver.add(Or(var == 1, var == 2))

# Enforce that in each category the assignments are unique.
solver.add(Eric != Arnold)
solver.add(photography != gardening)
solver.add(cat != dog)
solver.add(very_short != short)

# Clues:
# 1. The person who is very short is the photography enthusiast.
solver.add(very_short == photography)

# 2. Eric is the person who is very short.
solver.add(Eric == very_short)

# 3. The person who has a cat is somewhere to the right of the person who is very short.
# "Right" means that the house number of the cat holder is greater than that of the very short person.
solver.add(cat > very_short)

# Solve the puzzle.
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": []
        }
    }
    
    # Iterate through houses in order.
    for house in [1, 2]:
        # Determine the person by checking whose assigned house equals the current house.
        if model.evaluate(Eric).as_long() == house:
            name = "Eric"
        elif model.evaluate(Arnold).as_long() == house:
            name = "Arnold"
        else:
            name = ""
        
        # Determine the hobby.
        if model.evaluate(photography).as_long() == house:
            hobby = "photography"
        elif model.evaluate(gardening).as_long() == house:
            hobby = "gardening"
        else:
            hobby = ""
        
        # Determine the pet.
        if model.evaluate(cat).as_long() == house:
            pet = "cat"
        elif model.evaluate(dog).as_long() == house:
            pet = "dog"
        else:
            pet = ""
        
        # Determine the height.
        if model.evaluate(very_short).as_long() == house:
            height = "very short"
        elif model.evaluate(short).as_long() == house:
            height = "short"
        else:
            height = ""
        
        solution["solution"]["rows"].append([str(house), name, hobby, pet, height])
    
    # Output the solution as a JSON-formatted string.
    print(json.dumps(solution))
else:
    print("No solution found")