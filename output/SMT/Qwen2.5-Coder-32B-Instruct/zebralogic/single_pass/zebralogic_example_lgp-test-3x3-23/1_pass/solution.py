from z3 import *

# Create variables for each attribute of each person
names = [Int(f"name_{i}") for i in range(1, 4)]
occupations = [Int(f"occupation_{i}") for i in range(1, 4)]
hobbies = [Int(f"hobby_{i}") for i in range(1, 4)]

# Define constants for each name, occupation, and hobby
peter, arnold, eric = 1, 2, 3
doctor, teacher, engineer = 1, 2, 3
cooking, photography, gardening = 1, 2, 3

# Create a solver instance
solver = Solver()

# Add constraints for unique assignments of names, occupations, and hobbies
solver.add(Distinct(names))
solver.add(Distinct(occupations))
solver.add(Distinct(hobbies))

# Add constraints based on the clues
# Clue 1: The person who is a doctor and Eric are next to each other.
solver.add(Or(
    And(names[0] == eric, occupations[1] == doctor),
    And(names[1] == eric, occupations[0] == doctor),
    And(names[1] == eric, occupations[2] == doctor),
    And(names[2] == eric, occupations[1] == doctor)
))

# Clue 2: The person who loves cooking is directly left of the person who is a teacher.
solver.add(And(hobbies[0] == cooking, occupations[1] == teacher) |
           And(hobbies[1] == cooking, occupations[2] == teacher))

# Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
solver.add(Or(
    And(hobbies[0] == gardening, occupations[1] == doctor),
    And(hobbies[0] == gardening, occupations[2] == doctor),
    And(hobbies[1] == gardening, occupations[2] == doctor)
))

# Clue 4: The photography enthusiast is the person who is a teacher.
solver.add(And(hobbies[i] == photography, occupations[i] == teacher) for i in range(3))

# Clue 5: The person who is an engineer is Peter.
solver.add(And(names[i] == peter, occupations[i] == engineer) for i in range(3))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": []
        }
    }
    
    # Map the integer values back to their respective names, occupations, and hobbies
    name_map = {peter: "Peter", arnold: "Arnold", eric: "Eric"}
    occupation_map = {doctor: "doctor", teacher: "teacher", engineer: "engineer"}
    hobby_map = {cooking: "cooking", photography: "photography", gardening: "gardening"}
    
    for i in range(3):
        name_val = model.evaluate(names[i]).as_long()
        occupation_val = model.evaluate(occupations[i]).as_long()
        hobby_val = model.evaluate(hobbies[i]).as_long()
        
        solution["solution"]["rows"].append([
            str(i + 1),
            name_map[name_val],
            occupation_map[occupation_val],
            hobby_map[hobby_val]
        ])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")