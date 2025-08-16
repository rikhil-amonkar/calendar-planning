from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 6)
names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']

# Create dictionaries to map variables to Z3 variables
name_vars = {h: Int(f'name_{h}') for h in houses}
vacation_vars = {h: Int(f'vacation_{h}') for h in houses}
child_vars = {h: Int(f'child_{h}') for h in houses}
nationality_vars = {h: Int(f'nationality_{h}') for h in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([vacation_vars[h] for h in houses]))
solver.add(Distinct([child_vars[h] for h in houses]))
solver.add(Distinct([nationality_vars[h] for h in houses]))

# Map indices to actual values
name_map = {i: n for i, n in enumerate(names)}
vacation_map = {i: v for i, v in enumerate(vacations)}
child_map = {i: c for i, c in enumerate(children)}
nationality_map = {i: n for i, n in enumerate(nationalities)}

# Clue 1: The Norwegian is Peter.
solver.add(nationality_vars[1] == nationality_map.index('norwegian'))
solver.add(name_vars[1] == name_map.index('Peter'))

# Clue 2: The Swedish person is the person's child is named Bella.
solver.add(Or([And(nationality_vars[h] == nationality_map.index('swede'), child_vars[h] == child_map.index('Bella')) for h in houses]))

# Clue 3: The person who loves beach vacations is directly left of the person's child is named Samantha.
solver.add(Or([And(vacation_vars[h] == vacation_map.index('beach'), child_vars[h + 1] == child_map.index('Samantha')) for h in range(1, 5)]))

# Clue 4: The person's child is named Bella is not in the second house.
solver.add(child_vars[2] != child_map.index('Bella'))

# Clue 5: Alice is the British person.
solver.add(Or([And(name_vars[h] == name_map.index('Alice'), nationality_vars[h] == nationality_map.index('brit')) for h in houses]))

# Clue 6: The person who likes going on cruises is in the first house.
solver.add(vacation_vars[1] == vacation_map.index('cruise'))

# Clue 7: The person's child is named Meredith is in the fourth house.
solver.add(child_vars[4] == child_map.index('Meredith'))

# Clue 8: Eric is not in the fifth house.
solver.add(name_vars[5] != name_map.index('Eric'))

# Clue 9: The Swedish person is somewhere to the right of the Norwegian.
solver.add(Or([And(nationality_vars[n] == nationality_map.index('swede'), nationality_vars[h] == nationality_map.index('norwegian'), n > h) for n in range(2, 6) for h in range(1, n)]))

# Clue 10: There is one house between the person's child is named Fred and the person who prefers city breaks.
solver.add(Or([And(child_vars[h] == child_map.index('Fred'), vacation_vars[h + 2] == vacation_map.index('city')) for h in range(1, 4)] +
              [And(child_vars[h] == child_map.index('Fred'), vacation_vars[h - 2] == vacation_map.index('city')) for h in range(3, 6)]))

# Clue 11: Bob is the person who enjoys camping trips.
solver.add(Or([And(name_vars[h] == name_map.index('Bob'), vacation_vars[h] == vacation_map.index('camping')) for h in houses]))

# Clue 12: The Dane is in the fifth house.
solver.add(nationality_vars[5] == nationality_map.index('dane'))

# Clue 13: The person who enjoys camping trips is not in the fifth house.
solver.add(vacation_vars[5] != vacation_map.index('camping'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name = name_map[model.evaluate(name_vars[h]).as_long()]
        vacation = vacation_map[model.evaluate(vacation_vars[h]).as_long()]
        child = child_map[model.evaluate(child_vars[h]).as_long()]
        nationality = nationality_map[model.evaluate(nationality_vars[h]).as_long()]
        solution.append([str(h), name, vacation, child, nationality])
    
    print({
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": solution
        }
    })
else:
    print("No solution found")