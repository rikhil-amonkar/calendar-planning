from z3 import *
import json

# Define the attributes and their possible values
names = ["Peter", "Alice", "Eric", "Arnold"]
mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
heights = ["tall", "average", "short", "very short"]
educations = ["high school", "associate", "master", "bachelor"]

# Create position variables for each attribute and value
name_pos = [Int(f'name_pos_{v}') for v in range(4)]
mother_pos = [Int(f'mother_pos_{v}') for v in range(4)]
smoothie_pos = [Int(f'smoothie_pos_{v}') for v in range(4)]
height_pos = [Int(f'height_pos_{v}') for v in range(4)]
education_pos = [Int(f'education_pos_{v}') for v in range(4)]

solver = Solver()

# Add constraints for each attribute's positions to be distinct and in 0-3
for positions in [name_pos, mother_pos, smoothie_pos, height_pos, education_pos]:
    solver.add(Distinct(positions))
    for p in positions:
        solver.add(And(p >= 0, p <= 3))

# Add all the clues as constraints
# Clue 1: mother_pos[0] (Janelle) is in house 3 (index 2)
solver.add(mother_pos[0] == 2)

# Clue 2: Desert (smoothie 2) lover has master (education 2)
solver.add(smoothie_pos[2] == education_pos[2])

# Clue 3: Desert lover not in first house (index 0)
solver.add(smoothie_pos[2] != 0)

# Clue 4: very short (height 3) is left of high school (education 0)
solver.add(height_pos[3] < education_pos[0])

# Clue 5: Eric (name 2) and Cherry (smoothie 3) are next to each other
solver.add(Abs(name_pos[2] - smoothie_pos[3]) == 1)

# Clue 6: high school (education 0) not in third house (index 2)
solver.add(education_pos[0] != 2)

# Clue 7: Kailyn (mother 3) has associate (education 1)
solver.add(mother_pos[3] == education_pos[1])

# Clue 8: Cherry (smoothie 3) is Aniya's (mother 2) child
solver.add(smoothie_pos[3] == mother_pos[2])

# Clue 9: tall (height 0) is Janelle's (mother 0)
solver.add(height_pos[0] == mother_pos[0])

# Clue 10: Arnold (name 3) is to the right of average height (height 1)
solver.add(name_pos[3] > height_pos[1])

# Clue 11: Dragonfruit (smoothie 1) is directly left of short (height 2)
solver.add(smoothie_pos[1] + 1 == height_pos[2])

# Clue 12: tall (height 0) is Alice (name 1)
solver.add(height_pos[0] == name_pos[1])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    rows = []
    for house_idx in range(4):
        # Determine each attribute for the current house
        # Name
        name_val = None
        for v in range(4):
            if model[name_pos[v]].as_long() == house_idx:
                name_val = names[v]
                break
        # Mother
        mother_val = None
        for v in range(4):
            if model[mother_pos[v]].as_long() == house_idx:
                mother_val = mothers[v]
                break
        # Smoothie
        smoothie_val = None
        for v in range(4):
            if model[smoothie_pos[v]].as_long() == house_idx:
                smoothie_val = smoothies[v]
                break
        # Height
        height_val = None
        for v in range(4):
            if model[height_pos[v]].as_long() == house_idx:
                height_val = heights[v]
                break
        # Education
        education_val = None
        for v in range(4):
            if model[education_pos[v]].as_long() == house_idx:
                education_val = educations[v]
                break
        rows.append([str(house_idx + 1), name_val, mother_val, smoothie_val, height_val, education_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")