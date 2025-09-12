import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()
    
    # Define the attributes using EnumSort
    Name, (Eric, Alice, Peter, Arnold) = EnumSort('Name', ['Eric', 'Alice', 'Peter', 'Arnold'])
    HairColor, (blonde, black, red, brown) = EnumSort('HairColor', ['blonde', 'black', 'red', 'brown'])
    FavoriteSport, (swimming, soccer, basketball, tennis) = EnumSort('FavoriteSport', ['swimming', 'soccer', 'basketball', 'tennis'])
    
    # Create variables for each house's attributes
    names = [Const(f'name_{i}', Name) for i in range(1, 5)]
    hairs = [Const(f'hair_{i}', HairColor) for i in range(1, 5)]
    sports = [Const(f'sport_{i}', FavoriteSport) for i in range(1, 5)]
    
    # All attributes must be unique per category
    solver.add(Distinct(names))
    solver.add(Distinct(hairs))
    solver.add(Distinct(sports))
    
    # Add constraints from clues
    # Clue 1: The person who loves soccer is not in the second house.
    solver.add(sports[1] != soccer)
    
    # Clue 2: Eric is the person who has blonde hair.
    for i in range(4):
        solver.add(Implies(names[i] == Eric, hairs[i] == blonde))
    
    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    blonde_pos = Int('blonde_pos')
    basketball_pos = Int('basketball_pos')
    solver.add(blonde_pos >= 1, blonde_pos <= 4)
    solver.add(basketball_pos >= 1, basketball_pos <= 4)
    for i in range(4):
        solver.add(Implies(hairs[i] == blonde, blonde_pos == i+1))
        solver.add(Implies(sports[i] == basketball, basketball_pos == i+1))
    solver.add(blonde_pos > basketball_pos)
    
    # Clue 4: The person who has black hair is the person who loves tennis.
    for i in range(4):
        solver.add(Implies(hairs[i] == black, sports[i] == tennis))
        solver.add(Implies(sports[i] == tennis, hairs[i] == black))
    
    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    arnold_pos = Int('arnold_pos')
    red_hair_pos = Int('red_hair_pos')
    solver.add(arnold_pos >= 1, arnold_pos <= 4)
    solver.add(red_hair_pos >= 1, red_hair_pos <= 4)
    for i in range(4):
        solver.add(Implies(names[i] == Arnold, arnold_pos == i+1))
        solver.add(Implies(hairs[i] == red, red_hair_pos == i+1))
    solver.add(arnold_pos < red_hair_pos)
    
    # Clue 6: Alice is the person who loves swimming.
    for i in range(4):
        solver.add(Implies(names[i] == Alice, sports[i] == swimming))
    
    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    for i in range(3):
        solver.add(Implies(hairs[i] == red, hairs[i+1] == black))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map house attributes to strings
        name_map = {Eric: "Eric", Alice: "Alice", Peter: "Peter", Arnold: "Arnold"}
        hair_map = {blonde: "blonde", black: "black", red: "red", brown: "brown"}
        sport_map = {swimming: "swimming", soccer: "soccer", basketball: "basketball", tennis: "tennis"}
        
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = model.eval(names[i])
            hair_val = model.eval(hairs[i])
            sport_val = model.eval(sports[i])
            
            rows.append([
                house_num,
                name_map[name_val],
                hair_map[hair_val],
                sport_map[sport_val]
            ])
        
        # Create JSON output
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()