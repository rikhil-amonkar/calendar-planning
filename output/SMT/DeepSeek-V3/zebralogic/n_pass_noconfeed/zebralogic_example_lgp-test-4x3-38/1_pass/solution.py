from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    n_houses = 4
    houses = range(1, n_houses+1)
    
    # Define attributes
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
    flowers = ['carnations', 'roses', 'lilies', 'daffodils']
    
    # Create integer variables for each attribute's position
    name_pos = {name: Int(f'name_{name}') for name in names}
    mother_pos = {mother: Int(f'mother_{mother}') for mother in mothers}
    flower_pos = {flower: Int(f'flower_{flower}') for flower in flowers}
    
    # Each attribute must be in exactly one house (1-4)
    for attr_dict in [name_pos, mother_pos, flower_pos]:
        for attr in attr_dict:
            solver.add(And(attr_dict[attr] >= 1, attr_dict[attr] <= n_houses))
    
    # All attributes of the same type must have distinct positions
    for attr_dict in [name_pos, mother_pos, flower_pos]:
        solver.add(Distinct([attr_dict[attr] for attr in attr_dict]))
    
    # Clue 1: Alice is The person whose mother's name is Kailyn.
    solver.add(name_pos['Alice'] == mother_pos['Kailyn'])
    
    # Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
    solver.add(mother_pos['Janelle'] > name_pos['Arnold'])
    
    # Clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
    solver.add(name_pos['Peter'] > flower_pos['carnations'])
    
    # Clue 4: Eric is the person who loves a bouquet of daffodils.
    solver.add(name_pos['Eric'] == flower_pos['daffodils'])
    
    # Clue 5: Arnold is The person whose mother's name is Holly.
    solver.add(name_pos['Arnold'] == mother_pos['Holly'])
    
    # Clue 6: The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly.
    solver.add(flower_pos['carnations'] > mother_pos['Holly'])
    
    # Clue 7: The person who loves the bouquet of lilies is directly left of Alice.
    solver.add(flower_pos['lilies'] == name_pos['Alice'] - 1)
    
    # Clue 8: Alice is in the third house.
    solver.add(name_pos['Alice'] == 3)
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": []
            }
        }
        
        # For each house, find the attributes
        for house in houses:
            # Find name for this house
            name_val = None
            for name, pos_var in name_pos.items():
                if model.evaluate(pos_var).as_long() == house:
                    name_val = name
                    break
            
            # Find mother for this house
            mother_val = None
            for mother, pos_var in mother_pos.items():
                if model.evaluate(pos_var).as_long() == house:
                    mother_val = mother
                    break
            
            # Find flower for this house
            flower_val = None
            for flower, pos_var in flower_pos.items():
                if model.evaluate(pos_var).as_long() == house:
                    flower_val = flower
                    break
            
            result["solution"]["rows"].append([str(house), name_val, mother_val, flower_val])
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()