from z3 import *

# Define the variables
houses = range(1, 5)
names = ['Eric', 'Peter', 'Arnold', 'Alice']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
heights = ['tall', 'average', 'short', 'very short']
phone_models = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

# Create the solver
solver = Solver()

# Create variables for each characteristic for each house
name_vars = [String(f'name_{i}') for i in houses]
smoothie_vars = [String(f'smoothie_{i}') for i in houses]
cigar_vars = [String(f'cigar_{i}') for i in houses]
height_vars = [String(f'height_{i}') for i in houses]
phone_model_vars = [String(f'phone_model_{i}') for i in houses]

# Add domain constraints
for i in houses:
    solver.add(name_vars[i-1] == Or(*[name for name in names]))
    solver.add(smoothie_vars[i-1] == Or(*[smoothie for smoothie in smoothies]))
    solver.add(cigar_vars[i-1] == Or(*[cigar for cigar in cigars]))
    solver.add(height_vars[i-1] == Or(*[height for height in heights]))
    solver.add(phone_model_vars[i-1] == Or(*[phone_model for phone_model in phone_models]))

# Add uniqueness constraints
solver.add(Distinct(name_vars))
solver.add(Distinct(smoothie_vars))
solver.add(Distinct(cigar_vars))
solver.add(Distinct(height_vars))
solver.add(Distinct(phone_model_vars))

# Add clue constraints
# Clue 1
solver.add(smoothie_vars[0] == 'dragonfruit')
solver.add(name_vars[0] == 'Eric')

# Clue 2
solver.add(cigar_vars[i-1] == 'dunhill') == (smoothie_vars[i-1] == 'cherry' for i in houses)

# Clue 3
solver.add(phone_model_vars[0] == 'samsung galaxy s21') == (phone_model_vars[1] == 'iphone 13')
solver.add(phone_model_vars[1] == 'samsung galaxy s21') == (phone_model_vars[2] == 'iphone 13')
solver.add(phone_model_vars[2] == 'samsung galaxy s21') == (phone_model_vars[3] == 'iphone 13')

# Clue 4
for i in houses:
    for j in range(i+1, 5):
        solver.add((cigar_vars[j-1] == 'dunhill') == (height_vars[i-1] == 'very short'))

# Clue 5
for i in houses:
    for j in range(i+1, 5):
        solver.add((smoothie_vars[j-1] == 'watermelon') == (smoothie_vars[i-1] == 'desert'))

# Clue 6
solver.add(cigar_vars[i-1] == 'prince') == (phone_model_vars[i-1] == 'oneplus 9' for i in houses)

# Clue 7
solver.add(height_vars[2] == 'tall')

# Clue 8
solver.add(phone_model_vars[i-1] == 'iphone 13') == (height_vars[i-1] == 'very short' for i in houses)

# Clue 9
solver.add(cigar_vars[0] != 'blue master')

# Clue 10
solver.add(cigar_vars[i-1] == 'dunhill') == (height_vars[i-1] == 'short' for i in houses)

# Clue 11
solver.add(name_vars[2] != 'Peter')

# Clue 12
solver.add(phone_model_vars[i-1] == 'google pixel 6') == (name_vars[i-1] == 'Arnold' for i in houses)

# Clue 13
solver.add(smoothie_vars[i-1] == 'dragonfruit') == (cigar_vars[i-1] == 'pall mall' for i in houses)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in houses:
        name = model[name_vars[i-1]].as_string()[1:-1]
        smoothie = model[smoothie_vars[i-1]].as_string()[1:-1]
        cigar = model[cigar_vars[i-1]].as_string()[1:-1]
        height = model[height_vars[i-1]].as_string()[1:-1]
        phone_model = model[phone_model_vars[i-1]].as_string()[1:-1]
        solution.append([str(i), name, smoothie, cigar, height, phone_model])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")