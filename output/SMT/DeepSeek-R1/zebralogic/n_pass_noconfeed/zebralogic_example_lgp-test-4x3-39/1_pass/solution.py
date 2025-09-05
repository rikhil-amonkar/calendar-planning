import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Houses
    houses = [1, 2, 3, 4]
    
    # Attributes with integer mappings
    names = {"Eric": 0, "Alice": 1, "Peter": 2, "Arnold": 3}
    hair_colors = {"blonde": 0, "black": 1, "red": 2, "brown": 3}
    sports = {"swimming": 0, "soccer": 1, "basketball": 2, "tennis": 3}
    
    # Reverse mappings for output
    rev_names = {v: k for k, v in names.items()}
    rev_hair = {v: k for k, v in hair_colors.items()}
    rev_sports = {v: k for k, v in sports.items()}
    
    # Create Z3 variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in houses]
    hair_vars = [Int(f"hair_{i}") for i in houses]
    sport_vars = [Int(f"sport_{i}") for i in houses]
    
    # Constraint: All attributes are within their domains
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] <= 3))
        solver.add(And(hair_vars[i-1] >= 0, hair_vars[i-1] <= 3))
        solver.add(And(sport_vars[i-1] >= 0, sport_vars[i-1] <= 3))
    
    # Constraint: All attributes are distinct per category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(hair_vars))
    solver.add(Distinct(sport_vars))
    
    # Clue 1: The person who loves soccer is not in the second house.
    solver.add(sport_vars[1] != sports["soccer"])
    
    # Clue 2: Eric is the person who has blonde hair.
    for i in range(4):
        solver.add(Implies(name_vars[i] == names["Eric"], hair_vars[i] == hair_colors["blonde"]))
    
    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    # Find house indices for blonde hair and basketball
    blonde_house = Int("blonde_house")
    basketball_house = Int("basketball_house")
    solver.add(blonde_house >= 1, blonde_house <= 4)
    solver.add(basketball_house >= 1, basketball_house <= 4)
    for i in range(4):
        solver.add(Implies(hair_vars[i] == hair_colors["blonde"], blonde_house == i+1))
        solver.add(Implies(sport_vars[i] == sports["basketball"], basketball_house == i+1))
    solver.add(blonde_house > basketball_house)
    
    # Clue 4: The person who has black hair is the person who loves tennis.
    for i in range(4):
        solver.add(Implies(hair_vars[i] == hair_colors["black"], sport_vars[i] == sports["tennis"]))
    
    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    arnold_house = Int("arnold_house")
    red_hair_house = Int("red_hair_house")
    solver.add(arnold_house >= 1, arnold_house <= 4)
    solver.add(red_hair_house >= 1, red_hair_house <= 4)
    for i in range(4):
        solver.add(Implies(name_vars[i] == names["Arnold"], arnold_house == i+1))
        solver.add(Implies(hair_vars[i] == hair_colors["red"], red_hair_house == i+1))
    solver.add(arnold_house < red_hair_house)
    
    # Clue 6: Alice is the person who loves swimming.
    for i in range(4):
        solver.add(Implies(name_vars[i] == names["Alice"], sport_vars[i] == sports["swimming"]))
    
    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    for i in range(3):
        solver.add(Implies(
            hair_vars[i] == hair_colors["red"],
            And(hair_vars[i+1] == hair_colors["black"])
        ))
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare results
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = model.eval(name_vars[i]).as_long()
            hair_val = model.eval(hair_vars[i]).as_long()
            sport_val = model.eval(sport_vars[i]).as_long()
            
            name_str = rev_names[name_val]
            hair_str = rev_hair[hair_val]
            sport_str = rev_sports[sport_val]
            
            rows.append([house_num, name_str, hair_str, sport_str])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()