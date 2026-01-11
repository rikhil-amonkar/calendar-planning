from z3 import *

# Define the variables for the positions of each person and cigar
names = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']

# Create integer variables for the positions of each person and cigar
name_positions = [Int(f'name_{i}') for i in range(6)]
cigar_positions = [Int(f'cigar_{i}') for i in range(6)]

# Create the solver
solver = Solver()

# Add constraints for unique positions for names and cigars
solver.add(Distinct(name_positions))
solver.add(Distinct(cigar_positions))

# Constraint 1: Arnold is somewhere to the left of the person who smokes blends
solver.add(name_positions[names.index('Arnold')] < cigar_positions[cigars.index('blends')])

# Constraint 2: The person who smokes Blue Master is in the fifth house
solver.add(cigar_positions[cigars.index('blue master')] == 4)

# Constraint 3: Arnold is somewhere to the left of the Prince smoker
solver.add(name_positions[names.index('Arnold')] < cigar_positions[cigars.index('prince')])

# Constraint 4: There is one house between the person who smokes Yellow Monster and the person who smokes blends
solver.add(Abs(cigar_positions[cigars.index('yellow monster')] - cigar_positions[cigars.index('blends')]) == 2)

# Constraint 5: The person partial to Pall Mall is in the third house
solver.add(cigar_positions[cigars.index('pall mall')] == 2)

# Constraint 6: Eric is in the sixth house
solver.add(name_positions[names.index('Eric')] == 5)

# Constraint 7: Carol and Eric are next to each other
solver.add(Abs(name_positions[names.index('Carol')] - name_positions[names.index('Eric')]) == 1)

# Constraint 8: Peter is in the first house
solver.add(name_positions[names.index('Peter')] == 0)

# Constraint 9: Bob is in the third house
solver.add(name_positions[names.index('Bob')] == 2)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        name = names[model.evaluate(name_positions[i]).as_long()]
        cigar = cigars[model.evaluate(cigar_positions[i]).as_long()]
        solution.append([str(i+1), name, cigar])
    
    # Format the solution as a JSON string
    result = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")