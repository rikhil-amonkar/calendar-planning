from z3 import *

def solve_puzzle():
    # Define domains
    houses = [1, 2, 3, 4, 5]
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']

    # Create variables
    name_vars = {house: Int(f'name_{house}') for house in houses}
    color_vars = {house: Int(f'color_{house}') for house in houses}
    phone_vars = {house: Int(f'phone_{house}') for house in houses}
    occupation_vars = {house: Int(f'occupation_{house}') for house in houses}

    # Create solver
    solver = Solver()

    # Add domain constraints
    for house in houses:
        solver.add(name_vars[house] >= 0)
        solver.add(name_vars[house] < len(names))
        solver.add(color_vars[house] >= 0)
        solver.add(color_vars[house] < len(colors))
        solver.add(phone_vars[house] >= 0)
        solver.add(phone_vars[house] < len(phones))
        solver.add(occupation_vars[house] >= 0)
        solver.add(occupation_vars[house] < len(occupations))

    # All values must be unique
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([color_vars[house] for house in houses]))
    solver.add(Distinct([phone_vars[house] for house in houses]))
    solver.add(Distinct([occupation_vars[house] for house in houses]))

    # Clue constraints
    solver.add(name_vars[2] == names.index('Bob'))  # Clue 2
    solver.add(occupation_vars[houses.index(houses[-1])] != occupations.index('lawyer'))  # Clue 1
    solver.add(phone_vars[houses.index(houses[-1])] != phones.index('samsung galaxy s21'))  # Clue 8
    solver.add(phone_vars[houses.index(houses[-1])] != phones.index('oneplus 9'))  # Clue 6

    for i in range(len(houses) - 1):
        if i + 1 < len(houses):
            solver.add(Implies(occupation_vars[houses[i]] == occupations.index('lawyer'), occupation_vars[houses[i + 1]] != occupations.index('engineer')))  # Clue 1
            solver.add(Implies(phone_vars[houses[i]] == phones.index('samsung galaxy s21'), occupation_vars[houses[i + 1]] != occupations.index('lawyer')))  # Clue 8

    for i in range(len(houses) - 2):
        solver.add(Implies(phone_vars[houses[i]] == phones.index('google pixel 6'), Or(phone_vars[houses[i + 2]] == phones.index('huawei p50'), phone_vars[houses[i + 2]] == phones.index('google pixel 6'))))
        solver.add(Implies(phone_vars[houses[i + 2]] == phones.index('huawei p50'), Or(phone_vars[houses[i]] == phones.index('google pixel 6'), phone_vars[houses[i]] == phones.index('huawei p50'))))
        solver.add(Implies(phone_vars[houses[i + 2]] == phones.index('google pixel 6'), Or(phone_vars[houses[i]] == phones.index('huawei p50'), phone_vars[houses[i]] == phones.index('google pixel 6'))))

    solver.add(phone_vars[houses.index(houses[-1])] != phones.index('google pixel 6'))  # Clue 9
    solver.add(phone_vars[houses.index(houses[-1])] != phones.index('huawei p50'))  # Clue 9

    solver.add(occupation_vars[houses.index(houses[-1])] != occupations.index('teacher'))  # Clue 14

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        result = {}
        for house in houses:
            result[house] = {
                'Name': names[model[name_vars[house]].as_long()],
                'Color': colors[model[color_vars[house]].as_long()],
                'Phone': phones[model[phone_vars[house]].as_long()],
                'Occupation': occupations[model[occupation_vars[house]].as_long()]
            }
        return result
    else:
        return "No solution found"

# Call the function and print the result
print(solve_puzzle())