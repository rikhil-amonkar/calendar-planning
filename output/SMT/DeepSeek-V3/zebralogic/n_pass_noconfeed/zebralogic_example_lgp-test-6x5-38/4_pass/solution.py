# Define variables and indices
name_idx = {'Alice': 0, 'Bob': 1, 'Charlie': 2, 'David': 3, 'Eve': 4, 'Frank': 5}
car_model_idx = {'bmw 3 series': 0, 'audi a4': 1, 'mercedes c-class': 2, 'toyota camry': 3, 'honda accord': 4, 'ford fusion': 5}

# Create Z3 variables
name_vars = [Int(f'name_{i}') for i in range(1, 7)]
car_model_vars = [Int(f'car_model_{i}') for i in range(1, 7)]

# Add constraints that all variables are distinct and within valid ranges
for i in range(6):
    solver.add(And(name_vars[i] >= 0, name_vars[i] < 6))
    solver.add(And(car_model_vars[i] >= 0, car_model_vars[i] < 6))

solver.add(Distinct(name_vars))
solver.add(Distinct(car_model_vars))