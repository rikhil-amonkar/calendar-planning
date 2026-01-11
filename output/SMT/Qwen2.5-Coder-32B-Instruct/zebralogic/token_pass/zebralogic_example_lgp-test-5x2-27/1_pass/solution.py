from z3 import *

# Define the solver
solver = Solver()

# Define the domain for names and heights
names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
heights = ["very tall", "average", "tall", "very short", "short"]

# Create variables for the names and heights in each house
house_names = [String(f'name_{i}') for i in range(5)]
house_heights = [String(f'height_{i}') for i in range(5)]

# Add constraints for unique names and heights
solver.add(Distinct(house_names))
solver.add(Distinct(house_heights))

# Add constraints based on the clues
# Clue 1: The person who is short is in the second house.
solver.add(house_heights[1] == "short")

# Clue 2: Peter is directly left of Bob.
solver.add(Or(
    And(house_names[0] == "Peter", house_names[1] == "Bob"),
    And(house_names[1] == "Peter", house_names[2] == "Bob"),
    And(house_names[2] == "Peter", house_names[3] == "Bob"),
    And(house_names[3] == "Peter", house_names[4] == "Bob")
))

# Clue 3: Eric is somewhere to the left of Peter.
solver.add(Or(
    And(house_names[0] == "Eric", Or(house_names[1] == "Peter", house_names[2] == "Peter", house_names[3] == "Peter", house_names[4] == "Peter")),
    And(house_names[1] == "Eric", Or(house_names[2] == "Peter", house_names[3] == "Peter", house_names[4] == "Peter")),
    And(house_names[2] == "Eric", Or(house_names[3] == "Peter", house_names[4] == "Peter")),
    And(house_names[3] == "Eric", house_names[4] == "Peter")
))

# Clue 4: The person who is very tall is directly left of Peter.
solver.add(Or(
    And(house_names[0] == "Peter", house_heights[0] == "very tall"),
    And(house_names[1] == "Peter", house_heights[1] == "very tall"),
    And(house_names[2] == "Peter", house_heights[2] == "very tall"),
    And(house_names[3] == "Peter", house_heights[3] == "very tall")
))

# Clue 5: Alice is directly left of the person who has an average height.
solver.add(Or(
    And(house_names[0] == "Alice", house_heights[1] == "average"),
    And(house_names[1] == "Alice", house_heights[2] == "average"),
    And(house_names[2] == "Alice", house_heights[3] == "average"),
    And(house_names[3] == "Alice", house_heights[4] == "average")
))

# Clue 6: The person who is short and the person who is very short are next to each other.
solver.add(Or(
    And(house_heights[0] == "short", house_heights[1] == "very short"),
    And(house_heights[1] == "short", house_heights[0] == "very short"),
    And(house_heights[1] == "short", house_heights[2] == "very short"),
    And(house_heights[2] == "short", house_heights[1] == "very short"),
    And(house_heights[2] == "short", house_heights[3] == "very short"),
    And(house_heights[3] == "short", house_heights[2] == "very short"),
    And(house_heights[3] == "short", house_heights[4] == "very short"),
    And(house_heights[4] == "short", house_heights[3] == "very short")
))

# Clue 7: The person who has an average height is in the fifth house.
solver.add(house_heights[4] == "average")

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": []
        }
    }
    
    for i in range(5):
        name = model[house_names[i]].as_string()[1:-1]  # Remove quotes
        height = model[house_heights[i]].as_string()[1:-1]  # Remove quotes
        solution["solution"]["rows"].append([str(i+1), name, height])
    
    print(solution)
else:
    print("No solution found")