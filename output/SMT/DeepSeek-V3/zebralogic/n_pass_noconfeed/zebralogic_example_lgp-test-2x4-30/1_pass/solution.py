import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2]
    
    # Define the attributes
    names = ['Arnold', 'Eric']
    hair_colors = ['black', 'brown']
    sports = ['basketball', 'soccer']
    smoothies = ['desert', 'cherry']
    
    # Create variables for each attribute per house
    name_vars = {h: z3.Int(f'name_{h}') for h in houses}
    hair_vars = {h: z3.Int(f'hair_{h}') for h in houses}
    sport_vars = {h: z3.Int(f'sport_{h}') for h in houses}
    smoothie_vars = {h: z3.Int(f'smoothie_{h}') for h in houses}
    
    # Define the domain for each variable (0-indexed)
    for h in houses:
        solver.add(z3.And(name_vars[h] >= 0, name_vars[h] < len(names)))
        solver.add(z3.And(hair_vars[h] >= 0, hair_vars[h] < len(hair_colors)))
        solver.add(z3.And(sport_vars[h] >= 0, sport_vars[h] < len(sports)))
        solver.add(z3.And(smoothie_vars[h] >= 0, smoothie_vars[h] < len(smoothies)))
    
    # All attributes must be unique per category
    solver.add(z3.Distinct([name_vars[h] for h in houses]))
    solver.add(z3.Distinct([hair_vars[h] for h in houses]))
    solver.add(z3.Distinct([sport_vars[h] for h in houses]))
    solver.add(z3.Distinct([smoothie_vars[h] for h in houses]))
    
    # Clue 1: The Desert smoothie lover is Arnold.
    # Find Arnold's house and set smoothie to desert
    for h in houses:
        solver.add(z3.Implies(name_vars[h] == names.index('Arnold'), 
                             smoothie_vars[h] == smoothies.index('desert')))
    
    # Clue 2: The person who has brown hair is the person who loves basketball.
    for h in houses:
        solver.add(z3.Implies(hair_vars[h] == hair_colors.index('brown'),
                             sport_vars[h] == sports.index('basketball')))
    
    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
    # Find Arnold's house and black hair house, ensure Arnold's house < black hair house
    arnold_house = None
    black_hair_house = None
    
    # Create variables to track positions
    arnold_pos = z3.Int('arnold_pos')
    black_hair_pos = z3.Int('black_hair_pos')
    
    # Constrain positions
    for h in houses:
        solver.add(z3.Implies(name_vars[h] == names.index('Arnold'), arnold_pos == h))
        solver.add(z3.Implies(hair_vars[h] == hair_colors.index('black'), black_hair_pos == h))
    
    solver.add(arnold_pos < black_hair_pos)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        rows = []
        for h in houses:
            name_idx = model.evaluate(name_vars[h]).as_long()
            hair_idx = model.evaluate(hair_vars[h]).as_long()
            sport_idx = model.evaluate(sport_vars[h]).as_long()
            smoothie_idx = model.evaluate(smoothie_vars[h]).as_long()
            
            row = [
                str(h),
                names[name_idx],
                hair_colors[hair_idx],
                sports[sport_idx],
                smoothies[smoothie_idx]
            ]
            rows.append(row)
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()