from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define the houses
    n_houses = 5
    houses = range(1, n_houses+1)
    
    # Define attributes
    names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    smoothie_vars = [Int(f'smoothie_{i}') for i in houses]
    nationality_vars = [Int(f'nationality_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(smoothie_vars[i-1] >= 0, smoothie_vars[i-1] < len(smoothies)))
        solver.add(And(nationality_vars[i-1] >= 0, nationality_vars[i-1] < len(nationalities)))
    
    # All attributes are distinct within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(smoothie_vars))
    solver.add(Distinct(nationality_vars))
    
    # Create mapping for easier reference
    name_to_idx = {name: idx for idx, name in enumerate(names)}
    smoothie_to_idx = {smoothie: idx for idx, smoothie in enumerate(smoothies)}
    nationality_to_idx = {nationality: idx for idx, nationality in enumerate(nationalities)}
    
    # Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric.
    dragonfruit_idx = smoothie_to_idx['dragonfruit']
    eric_idx = name_to_idx['Eric']
    
    # Find house with dragonfruit smoothie and house with Eric
    dragonfruit_house = Int('dragonfruit_house')
    eric_house = Int('eric_house')
    
    solver.add(dragonfruit_house >= 1, dragonfruit_house <= 5)
    solver.add(eric_house >= 1, eric_house <= 5)
    
    # Connect variables to actual houses
    for i in houses:
        solver.add(Implies(smoothie_vars[i-1] == dragonfruit_idx, dragonfruit_house == i))
        solver.add(Implies(name_vars[i-1] == eric_idx, eric_house == i))
    
    solver.add(dragonfruit_house < eric_house)
    
    # Clue 2: The Dragonfruit smoothie lover is in the second house.
    solver.add(dragonfruit_house == 2)
    
    # Clue 3: Peter is not in the first house.
    peter_idx = name_to_idx['Peter']
    solver.add(name_vars[0] != peter_idx)
    
    # Clue 4: The Dane and the British person are next to each other.
    dane_idx = nationality_to_idx['dane']
    brit_idx = nationality_to_idx['brit']
    
    dane_house = Int('dane_house')
    brit_house = Int('brit_house')
    
    solver.add(dane_house >= 1, dane_house <= 5)
    solver.add(brit_house >= 1, brit_house <= 5)
    
    for i in houses:
        solver.add(Implies(nationality_vars[i-1] == dane_idx, dane_house == i))
        solver.add(Implies(nationality_vars[i-1] == brit_idx, brit_house == i))
    
    solver.add(Or(dane_house == brit_house + 1, dane_house == brit_house - 1))
    
    # Clue 5: The Desert smoothie lover is not in the fifth house.
    desert_idx = smoothie_to_idx['desert']
    solver.add(smoothie_vars[4] != desert_idx)
    
    # Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
    swede_idx = nationality_to_idx['swede']
    swede_house = Int('swede_house')
    solver.add(swede_house >= 1, swede_house <= 5)
    
    for i in houses:
        solver.add(Implies(nationality_vars[i-1] == swede_idx, swede_house == i))
    
    solver.add(swede_house < dragonfruit_house)
    
    # Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane.
    lime_idx = smoothie_to_idx['lime']
    lime_house = Int('lime_house')
    solver.add(lime_house >= 1, lime_house <= 5)
    
    for i in houses:
        solver.add(Implies(smoothie_vars[i-1] == lime_idx, lime_house == i))
    
    solver.add(Or(lime_house == dane_house + 3, lime_house == dane_house - 3))
    
    # Clue 8: Bob is the Dane.
    bob_idx = name_to_idx['Bob']
    for i in houses:
        solver.add(Implies(name_vars[i-1] == bob_idx, nationality_vars[i-1] == dane_idx))
    
    # Clue 9: Alice is the Norwegian.
    alice_idx = name_to_idx['Alice']
    norwegian_idx = nationality_to_idx['norwegian']
    for i in houses:
        solver.add(Implies(name_vars[i-1] == alice_idx, nationality_vars[i-1] == norwegian_idx))
    
    # Clue 10: Alice is in the third house.
    solver.add(name_vars[2] == alice_idx)
    
    # Clue 11: The Watermelon smoothie lover is in the third house.
    watermelon_idx = smoothie_to_idx['watermelon']
    solver.add(smoothie_vars[2] == watermelon_idx)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": []
            }
        }
        
        for i in houses:
            name_val = model.eval(name_vars[i-1]).as_long()
            smoothie_val = model.eval(smoothie_vars[i-1]).as_long()
            nationality_val = model.eval(nationality_vars[i-1]).as_long()
            
            row = [
                str(i),
                names[name_val],
                smoothies[smoothie_val],
                nationalities[nationality_val]
            ]
            solution["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()