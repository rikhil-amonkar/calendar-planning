from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each house, name, and cigar
houses = range(1, 7)
names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

# Dictionaries to map names and cigars to their respective house numbers
name_vars = {name: Int(name) for name in names}
cigar_vars = {cigar: Int(cigar) for cigar in cigars}

# Constraints for each variable to be within the range of houses
for var in list(name_vars.values()) + list(cigar_vars.values()):
    solver.add(And(var >= 1, var <= 6))

# All names and cigars must be unique
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(cigar_vars.values())))

# Clue 1: Arnold is somewhere to the left of the person who smokes many unique blends.
solver.add(name_vars["Arnold"] < cigar_vars["blends"])

# Clue 2: The person who smokes Blue Master is in the fifth house.
solver.add(cigar_vars["blue master"] == 5)

# Clue 3: Arnold is somewhere to the left of the Prince smoker.
solver.add(name_vars["Arnold"] < cigar_vars["prince"])

# Clue 4: There is one house between the person who smokes Yellow Monster and the person who smokes many unique blends.
solver.add(Abs(cigar_vars["yellow monster"] - cigar_vars["blends"]) == 2)

# Clue 5: The person partial to Pall Mall is in the third house.
solver.add(cigar_vars["pall mall"] == 3)

# Clue 6: Eric is in the sixth house.
solver.add(name_vars["Eric"] == 6)

# Clue 7: Carol and Eric are next to each other.
solver.add(Abs(name_vars["Carol"] - name_vars["Eric"]) == 1)

# Clue 8: Peter is in the first house.
solver.add(name_vars["Peter"] == 1)

# Clue 9: Bob is in the third house.
solver.add(name_vars["Bob"] == 3)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    # Create a dictionary to map house numbers to names and cigars
    house_to_name = {i: None for i in houses}
    house_to_cigar = {i: None for i in houses}
    
    for name, var in name_vars.items():
        house_to_name[model.evaluate(var).as_long()] = name
    
    for cigar, var in cigar_vars.items():
        house_to_cigar[model.evaluate(var).as_long()] = cigar
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": []
        }
    }
    
    for house in houses:
        solution["solution"]["rows"].append([str(house), house_to_name[house], house_to_cigar[house]])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")