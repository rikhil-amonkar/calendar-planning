from z3 import *

# Define EnumSorts
names_sort, (Eric, Peter, Arnold, Alice, Bob) = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob'])
mothers_sort, (Kailyn, Janelle, Aniya, Penny, Holly) = EnumSort('Mother', ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly'])
heights_sort, (average, very_short, short, very_tall, tall) = EnumSort('Height', ['average', 'very short', 'short', 'very tall', 'tall'])

# Create variables for each house (0-based index for 1-5 houses)
names = [Const(f'name_{i+1}', names_sort) for i in range(5)]
mothers = [Const(f'mother_{i+1}', mothers_sort) for i in range(5)]
heights = [Const(f'height_{i+1}', heights_sort) for i in range(5)]

solver = Solver()

# Add distinct constraints
solver.add(Distinct(names))
solver.add(Distinct(mothers))
solver.add(Distinct(heights))

# Clue 1: Alice is the person whose mother is Aniya
for i in range(5):
    solver.add(Implies(mothers[i] == Aniya, names[i] == Alice))

# Clue 3: Mother Janelle is Bob
for i in range(5):
    solver.add(Implies(mothers[i] == Janelle, names[i] == Bob))

# Clue 10: Eric's mother is Kailyn
for i in range(5):
    solver.add(Implies(names[i] == Eric, mothers[i] == Kailyn))

# Clue 6: Arnold is very tall
for i in range(5):
    solver.add(Implies(names[i] == Arnold, heights[i] == very_tall))

# Clue 4: Peter not in house 2 (index 1)
solver.add(names[1] != Peter)

# Clue 8: Eric not in house 5 (index 4)
solver.add(names[4] != Eric)

# Clue 11: very short in house 5 (index 4)
solver.add(heights[4] == very_short)

# Clue 5: short directly left of Arnold
clue5 = Or([And(heights[i] == short, names[i+1] == Arnold) for i in range(4)])
solver.add(clue5)

# Clue 7: Bob directly left of average
clue7 = Or([And(names[i] == Bob, heights[i+1] == average) for i in range(4)])
solver.add(clue7)

# Clue 2: average left of Penny's mother
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(heights[i] == average, mothers[j] == Penny), i < j))

# Clue 9: Holly's mother is to the left of Arnold
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(mothers[i] == Holly, names[j] == Arnold), i < j))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the solution for each house
    solution = []
    for i in range(5):
        house_num = i + 1
        name_val = model.eval(names[i])
        mother_val = model.eval(mothers[i])
        height_val = model.eval(heights[i])
        solution.append([str(house_num), name_val.decl().name(), mother_val.decl().name(), height_val.decl().name()])
    # Now format into the required JSON structure
    import json
    json_output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")