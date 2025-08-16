import json
from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5]

    # Define the names and heights
    names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']

    # Create variables for each house's name and height
    name_vars = {house: Int(f'name_{house}') for house in houses}
    height_vars = {house: Int(f'height_{house}') for house in houses}

    # Add constraints for names: each name is unique and corresponds to one of the given names
    s.add(Distinct([name_vars[house] for house in houses]))
    for house in houses:
        s.add(name_vars[house] >= 0, name_vars[house] < len(names))

    # Add constraints for heights: each height is unique and corresponds to one of the given heights
    s.add(Distinct([height_vars[house] for house in houses]))
    for house in houses:
        s.add(height_vars[house] >= 0, height_vars[house] < len(heights))

    # Clue 1: The person who is short is in the second house.
    short_index = heights.index('short')
    s.add(height_vars[2] == short_index)

    # Clue 2: Peter is directly left of Bob.
    peter_index = names.index('Peter')
    bob_index = names.index('Bob')
    for house in houses[:-1]:
        s.add(Implies(name_vars[house] == peter_index, name_vars[house + 1] == bob_index))

    # Clue 3: Eric is somewhere to the left of Peter.
    eric_index = names.index('Eric')
    for house in houses:
        s.add(Implies(name_vars[house] == peter_index, 
                      Or([name_vars[h] == eric_index for h in range(1, house)])))

    # Clue 4: The person who is very tall is directly left of Peter.
    very_tall_index = heights.index('very tall')
    for house in houses[:-1]:
        s.add(Implies(name_vars[house + 1] == peter_index, 
                      height_vars[house] == very_tall_index))

    # Clue 5: Alice is directly left of the person who has an average height.
    alice_index = names.index('Alice')
    average_index = heights.index('average')
    for house in houses[:-1]:
        s.add(Implies(name_vars[house] == alice_index, 
                      height_vars[house + 1] == average_index))

    # Clue 6: The person who is short and the person who is very short are next to each other.
    very_short_index = heights.index('very short')
    for house in houses[:-1]:
        s.add(Or(
            And(height_vars[house] == short_index, height_vars[house + 1] == very_short_index),
            And(height_vars[house + 1] == short_index, height_vars[house] == very_short_index)
        ))

    # Clue 7: The person who has an average height is in the fifth house.
    s.add(height_vars[5] == average_index)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": []
            }
        }
        
        for house in houses:
            name_val = model.evaluate(name_vars[house]).as_long()
            height_val = model.evaluate(height_vars[house]).as_long()
            solution["solution"]["rows"].append([
                str(house),
                names[name_val],
                heights[height_val]
            ])
        
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Height"], "rows": []}}

# Solve the problem and print the result
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))