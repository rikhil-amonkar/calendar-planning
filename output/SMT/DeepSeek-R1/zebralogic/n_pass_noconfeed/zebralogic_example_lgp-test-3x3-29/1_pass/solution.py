import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()
    
    # Define enums for attributes
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Peter')
    Name.declare('Arnold')
    Name = Name.create()
    
    Mother = Datatype('Mother')
    Mother.declare('Holly')
    Mother.declare('Aniya')
    Mother.declare('Janelle')
    Mother = Mother.create()
    
    Food = Datatype('Food')
    Food.declare('pizza')
    Food.declare('grilled_cheese')
    Food.declare('spaghetti')
    Food = Food.create()
    
    # Create variables for each house
    houses = [1, 2, 3]
    names = [Const(f'n_{i}', Name) for i in houses]
    mothers = [Const(f'm_{i}', Mother) for i in houses]
    foods = [Const(f'f_{i}', Food) for i in houses]
    
    # Add uniqueness constraints
    solver.add(Distinct(names))
    solver.add(Distinct(mothers))
    solver.add(Distinct(foods))
    
    # Clue 1: The spaghetti eater and Peter are adjacent
    spaghetti_house = [foods[i] == Food.spaghetti for i in range(3)]
    peter_house = [names[i] == Name.Peter for i in range(3)]
    adjacent = Or(
        And(spaghetti_house[0], peter_house[1]),
        And(spaghetti_house[1], Or(peter_house[0], peter_house[2])),
        And(spaghetti_house[2], peter_house[1])
    )
    solver.add(adjacent)
    
    # Clue 2: Grilled cheese is directly left of Aniya's mother
    grilled_cheese_house = [foods[i] == Food.grilled_cheese for i in range(3)]
    aniya_house = [mothers[i] == Mother.Aniya for i in range(3)]
    left_of = Or(
        And(grilled_cheese_house[0], aniya_house[1]),
        And(grilled_cheese_house[1], aniya_house[2])
    )
    solver.add(left_of)
    
    # Clue 3: Grilled cheese eater is Eric
    for i in range(3):
        solver.add(Implies(foods[i] == Food.grilled_cheese, names[i] == Name.Eric))
    
    # Clue 4: Peter's mother is Holly
    for i in range(3):
        solver.add(Implies(names[i] == Name.Peter, mothers[i] == Mother.Holly))
    
    # Check and get the solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map house numbers to their attributes
        solution_rows = []
        for i in range(3):
            house_num = str(i + 1)
            name_val = model.eval(names[i])
            mother_val = model.eval(mothers[i])
            food_val = model.eval(foods[i])
            
            # Convert enum values to strings
            name_str = str(name_val)
            mother_str = str(mother_val)
            food_str = str(food_val)
            
            # Replace underscores with spaces for grilled cheese
            if food_str == 'grilled_cheese':
                food_str = 'grilled cheese'
                
            solution_rows.append([house_num, name_str, mother_str, food_str])
        
        # Create the JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Food"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()