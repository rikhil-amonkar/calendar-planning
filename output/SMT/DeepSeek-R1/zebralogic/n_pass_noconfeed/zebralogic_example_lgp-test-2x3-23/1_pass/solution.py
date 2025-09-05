from z3 import *
import json

def main():
    # Define enums for attributes
    NameSort, (Eric, Arnold) = EnumSort('NameSort', ['Eric', 'Arnold'])
    ChildSort, (Bella, Fred) = EnumSort('ChildSort', ['Bella', 'Fred'])
    FoodSort, (grilled_cheese, pizza) = EnumSort('FoodSort', ['grilled cheese', 'pizza'])
    
    # Create variables for each house and attribute
    variables = {}
    for house in [1, 2]:
        variables[f'name{house}'] = Const(f'name{house}', NameSort)
        variables[f'child{house}'] = Const(f'child{house}', ChildSort)
        variables[f'food{house}'] = Const(f'food{house}', FoodSort)
    
    s = Solver()
    
    # All attributes are unique per category
    s.add(Distinct([variables['name1'], variables['name2']]))
    s.add(Distinct([variables['child1'], variables['child2']]))
    s.add(Distinct([variables['food1'], variables['food2']]))
    
    # Clue 1: The person who is a pizza lover is Arnold.
    s.add(Implies(variables['food1'] == pizza, variables['name1'] == Arnold))
    s.add(Implies(variables['food2'] == pizza, variables['name2'] == Arnold))
    
    # Clue 2: The person who loves eating grilled cheese is directly left of the person whose child is named Fred.
    s.add(And(variables['food1'] == grilled_cheese, variables['child2'] == Fred))
    
    if s.check() == sat:
        m = s.model()
        rows = []
        for house in [1, 2]:
            name_val = m.evaluate(variables[f'name{house}'])
            child_val = m.evaluate(variables[f'child{house}'])
            food_val = m.evaluate(variables[f'food{house}'])
            rows.append([str(house), str(name_val), str(child_val), str(food_val)])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print('{"solution": {}}')

if __name__ == "__main__":
    main()