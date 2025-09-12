from z3 import *

def solve_puzzle():
    # Define the variables
    houses = [Int(f'house_{i}') for i in range(1, 6)]
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']

    # Create the solver
    solver = Solver()

    # Define the domain for each variable
    for var in houses + names + vacations + children + nationalities:
        if isinstance(var, Int):
            solver.add(var >= 1)
            solver.add(var <= 5)

    # Ensure all values are distinct
    solver.add(Distinct(houses))
    solver.add(Distinct(names))
    solver.add(Distinct(vacations))
    solver.add(Distinct(children))
    solver.add(Distinct(nationalities))

    # Define the mappings
    name_map = {name: Int(f'name_{name}') for name in names}
    vacation_map = {vacation: Int(f'vacation_{vacation}') for vacation in vacations}
    child_map = {child: Int(f'child_{child}') for child in children}
    nationality_map = {nationality: Int(f'nationality_{nationality}') for nationality in nationalities}

    # Add the clues as constraints
    solver.add(name_map['Peter'] == nationality_map['norwegian'])
    solver.add(child_map['Bella'] == nationality_map['swede'])
    solver.add(vacation_map['beach'] + 1 == child_map['Samantha'])
    solver.add(child_map['Bella'] != 2)
    solver.add(name_map['Alice'] == nationality_map['brit'])
    solver.add(vacation_map['cruise'] == 1)
    solver.add(child_map['Meredith'] == 4)
    solver.add(name_map['Eric'] != 5)
    solver.add(nationality_map['swede'] > nationality_map['norwegian'])
    solver.add(Abs(child_map['Fred'] - vacation_map['city']) == 2)
    solver.add(name_map['Bob'] == vacation_map['camping'])
    solver.add(nationality_map['dane'] == 5)
    solver.add(vacation_map['camping'] != 5)

    # Map the names to houses
    for name, house in name_map.items():
        solver.add(Or([house == h for h in houses]))

    # Map the vacations to houses
    for vacation, house in vacation_map.items():
        solver.add(Or([house == h for h in houses]))

    # Map the children to houses
    for child, house in child_map.items():
        solver.add(Or([house == h for h in houses]))

    # Map the nationalities to houses
    for nationality, house in nationality_map.items():
        solver.add(Or([house == h for h in houses]))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": []
            }
        }

        # Extract the solution
        for house in range(1, 6):
            name = next(name for name, var in name_map.items() if model.evaluate(var) == house)
            vacation = next(vacation for vacation, var in vacation_map.items() if model.evaluate(var) == house)
            child = next(child for child, var in child_map.items() if model.evaluate(var) == house)
            nationality = next(nationality for nationality, var in nationality_map.items() if model.evaluate(var) == house)
            result["solution"]["rows"].append([str(house), name, vacation, child, nationality])

        import json
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

solve_puzzle()