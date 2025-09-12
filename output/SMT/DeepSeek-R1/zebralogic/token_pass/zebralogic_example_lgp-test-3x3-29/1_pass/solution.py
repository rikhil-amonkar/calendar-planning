from z3 import *
import json

def main():
    # Define the attributes using EnumSort
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
    names = [Const(f'name_{i}', Name) for i in houses]
    mothers = [Const(f'mother_{i}', Mother) for i in houses]
    foods = [Const(f'food_{i}', Food) for i in houses]
    
    s = Solver()
    
    # All attributes are unique
    s.add(Distinct(names))
    s.add(Distinct(mothers))
    s.add(Distinct(foods))
    
    # Clue 3: Grilled cheese eater is Eric
    for i in houses:
        s.add(Implies(foods[i-1] == Food.grilled_cheese, names[i-1] == Name.Eric))
    
    # Clue 4: Peter's mother is Holly
    for i in houses:
        s.add(Implies(names[i-1] == Name.Peter, mothers[i-1] == Mother.Holly))
    
    # Clue 2: Grilled cheese left of Aniya's mother
    s.add(Or(
        And(foods[0] == Food.grilled_cheese, mothers[1] == Mother.Aniya),
        And(foods[1] == Food.grilled_cheese, mothers[2] == Mother.Aniya)
    ))
    # Grilled cheese cannot be in house 3
    s.add(foods[2] != Food.grilled_cheese)
    
    # Clue 1: Spaghetti eater and Peter are adjacent
    s.add(Or(
        And(names[0] == Name.Peter, foods[1] == Food.spaghetti),
        And(names[1] == Name.Peter, Or(foods[0] == Food.spaghetti, foods[2] == Food.spaghetti)),
        And(names[2] == Name.Peter, foods[1] == Food.spaghetti)
    ))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        solution = {"solution": {"header": ["House", "Name", "Mother", "Food"], "rows": []}}
        for i in houses:
            idx = i-1
            name_val = m.eval(names[idx])
            mother_val = m.eval(mothers[idx])
            food_val = m.eval(foods[idx])
            
            # Convert Z3 values to strings
            name_str = str(name_val).split('!')[0]
            mother_str = str(mother_val).split('!')[0]
            food_str = str(food_val).split('!')[0]
            
            solution["solution"]["rows"].append([str(i), name_str, mother_str, food_str])
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()