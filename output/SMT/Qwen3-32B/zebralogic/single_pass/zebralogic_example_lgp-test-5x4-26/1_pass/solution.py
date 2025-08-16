from z3 import *

# Define EnumSorts
Name, (Alice, Peter, Bob, Eric, Arnold) = EnumSort('Name', ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold'])
Height, (vs, s, t, a, vt) = EnumSort('Height', ['very short', 'short', 'tall', 'average', 'very tall'])
Mother, (Janelle, Kailyn, Penny, Holly, Aniya) = EnumSort('Mother', ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya'])
HairColor, (blonde, black, gray, red, brown) = EnumSort('HairColor', ['blonde', 'black', 'gray', 'red', 'brown'])

# Create variables for each house (0-based index for 5 houses)
names = [Const(f'Name_{i}', Name) for i in range(5)]
heights = [Const(f'Height_{i}', Height) for i in range(5)]
mothers = [Const(f'Mother_{i}', Mother) for i in range(5)]
hair_colors = [Const(f'HairColor_{i}', HairColor) for i in range(5)]

solver = Solver()

# Add distinct constraints
solver.add(Distinct(names))
solver.add(Distinct(heights))
solver.add(Distinct(mothers))
solver.add(Distinct(hair_colors))

# Add clues as constraints
# Clue 14: Kailyn is in house 3 (index 2)
solver.add(mothers[2] == Kailyn)

# Clue 8: Bob is in house 5 (index 4)
solver.add(names[4] == Bob)

# Clue 5: Eric has black hair
for i in range(5):
    solver.add(Implies(names[i] == Eric, hair_colors[i] == black))

# Clue 9: Peter has red hair
for i in range(5):
    solver.add(Implies(names[i] == Peter, hair_colors[i] == red))

# Clue 11: Arnold has brown hair
for i in range(5):
    solver.add(Implies(names[i] == Arnold, hair_colors[i] == brown))

# Clue 1: Tall is Holly's mother
for i in range(5):
    solver.add(Implies(heights[i] == t, mothers[i] == Holly))

# Clue 6: Very short is Penny's mother
for i in range(5):
    solver.add(Implies(heights[i] == vs, mothers[i] == Penny))

# Clue 4: Black hair not in house 4 (index 3)
solver.add(hair_colors[3] != black)

# Clue 7: Eric and gray are adjacent
for i in range(5):
    cond = []
    if i > 0:
        cond.append(hair_colors[i-1] == gray)
    if i < 4:
        cond.append(hair_colors[i+1] == gray)
    if cond:
        solver.add(Implies(names[i] == Eric, Or(cond)))

# Clue 2: average and short are 3 apart
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(heights[i] == a, heights[j] == s), Or(i - j == 3, j - i == 3)))

# Clue 3: Gray is directly left of Janelle
solver.add(Or([And(hair_colors[i] == gray, mothers[i+1] == Janelle) for i in range(4)]))

# Clue 10: Kailyn's mother (house 3) is directly left of short → short is in house 4 (index 3)
solver.add(heights[3] == s)

# Clue 12: Brown is left of Janelle
solver.add(Or([And(hair_colors[i] == brown, mothers[j] == Janelle, i < j) for i in range(5) for j in range(5)]))

# Clue 13: Aniya and Penny (very short) are adjacent
solver.add(Or([And(mothers[i] == Aniya, mothers[j] == Penny, Or(i - j == 1, j - i == 1)) for i in range(5) for j in range(5)]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution
    solution = []
    for i in range(5):
        house_num = i + 1
        name_val = model.evaluate(names[i]).decl().name()
        height_val = model.evaluate(heights[i]).decl().name()
        mother_val = model.evaluate(mothers[i]).decl().name()
        hair_val = model.evaluate(hair_colors[i]).decl().name()
        solution.append([str(house_num), name_val, height_val, mother_val, hair_val])
    # Output the JSON
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found.")