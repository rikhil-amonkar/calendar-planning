import json
from z3 import *

def main():
    solver = Solver()
    num_houses = 2

    # Create Z3 integer variables for each attribute per house.
    # For names: 0 = Arnold, 1 = Eric
    # For hair colors: 0 = black, 1 = brown
    # For favorite sports: 0 = basketball, 1 = soccer
    # For smoothies: 0 = desert, 1 = cherry
    names = [Int(f"name_{i}") for i in range(num_houses)]
    hair = [Int(f"hair_{i}") for i in range(num_houses)]
    sport = [Int(f"sport_{i}") for i in range(num_houses)]
    smoothie = [Int(f"smoothie_{i}") for i in range(num_houses)]
    
    # Each attribute variable can only be 0 or 1.
    for i in range(num_houses):
        solver.add(Or(names[i] == 0, names[i] == 1))
        solver.add(Or(hair[i] == 0, hair[i] == 1))
        solver.add(Or(sport[i] == 0, sport[i] == 1))
        solver.add(Or(smoothie[i] == 0, smoothie[i] == 1))
    
    # Each attribute must be unique across the houses.
    solver.add(Distinct(names))
    solver.add(Distinct(hair))
    solver.add(Distinct(sport))
    solver.add(Distinct(smoothie))
    
    # Clue 1: The Desert smoothie lover is Arnold.
    # This means: if a house's name is Arnold (0), then its smoothie must be desert (0), and vice versa.
    for i in range(num_houses):
        solver.add(Implies(names[i] == 0, smoothie[i] == 0))
        solver.add(Implies(smoothie[i] == 0, names[i] == 0))
    
    # Clue 2: The person who has brown hair is the person who loves basketball.
    # For hair: brown is 1; for sport: basketball is 0.
    for i in range(num_houses):
        solver.add(Implies(hair[i] == 1, sport[i] == 0))
        solver.add(Implies(sport[i] == 0, hair[i] == 1))
    
    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
    # Houses are numbered 1 and 2 from left to right (indices 0 and 1 respectively).
    # In a 2-house puzzle, the only way to satisfy a left/right constraint is:
    solver.add(names[0] == 0)   # House 1 must be occupied by Arnold.
    solver.add(hair[1] == 0)    # House 2 must have black hair.
    
    if solver.check() == sat:
        model = solver.model()
        
        # Maps from integer values to attribute string names.
        name_map = {0: "Arnold", 1: "Eric"}
        hair_map = {0: "black", 1: "brown"}
        sport_map = {0: "basketball", 1: "soccer"}
        smoothie_map = {0: "desert", 1: "cherry"}
        
        rows = []
        for i in range(num_houses):
            house_num = str(i + 1)
            name_val = model.evaluate(names[i]).as_long()
            hair_val = model.evaluate(hair[i]).as_long()
            sport_val = model.evaluate(sport[i]).as_long()
            smoothie_val = model.evaluate(smoothie[i]).as_long()
            
            row = [
                house_num,
                name_map[name_val],
                hair_map[hair_val],
                sport_map[sport_val],
                smoothie_map[smoothie_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()