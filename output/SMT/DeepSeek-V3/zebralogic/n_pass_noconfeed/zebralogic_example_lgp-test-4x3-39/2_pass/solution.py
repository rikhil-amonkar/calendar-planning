import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define the houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    hair_colors = ['blonde', 'black', 'red', 'brown']
    sports = ['swimming', 'soccer', 'basketball', 'tennis']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    hair_vars = [Int(f'hair_{i}') for i in houses]
    sport_vars = [Int(f'sport_{i}') for i in houses]
    
    # Constraint: All attributes must be within valid range (0-3)
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < 4))
        solver.add(And(hair_vars[i-1] >= 0, hair_vars[i-1] < 4))
        solver.add(And(sport_vars[i-1] >= 0, sport_vars[i-1] < 4))
    
    # Constraint: All names are distinct
    solver.add(Distinct(name_vars))
    
    # Constraint: All hair colors are distinct
    solver.add(Distinct(hair_vars))
    
    # Constraint: All sports are distinct
    solver.add(Distinct(sport_vars))
    
    # Clue 1: The person who loves soccer is not in the second house.
    soccer_idx = sports.index('soccer')
    solver.add(sport_vars[1] != soccer_idx)  # house 2 is index 1
    
    # Clue 2: Eric is the person who has blonde hair.
    eric_idx = names.index('Eric')
    blonde_idx = hair_colors.index('blonde')
    for i in houses:
        solver.add(Implies(name_vars[i-1] == eric_idx, hair_vars[i-1] == blonde_idx))
    
    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    basketball_idx = sports.index('basketball')
    # Create variables to track positions
    blonde_house = Int('blonde_house')
    basketball_house = Int('basketball_house')
    
    for i in houses:
        solver.add(Implies(hair_vars[i-1] == blonde_idx, blonde_house == i))
        solver.add(Implies(sport_vars[i-1] == basketball_idx, basketball_house == i))
    
    solver.add(blonde_house > basketball_house)
    
    # Clue 4: The person who has black hair is the person who loves tennis.
    black_idx = hair_colors.index('black')
    tennis_idx = sports.index('tennis')
    for i in houses:
        solver.add(Implies(hair_vars[i-1] == black_idx, sport_vars[i-1] == tennis_idx))
    
    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    arnold_idx = names.index('Arnold')
    red_idx = hair_colors.index('red')
    
    arnold_house = Int('arnold_house')
    red_hair_house = Int('red_hair_house')
    
    for i in houses:
        solver.add(Implies(name_vars[i-1] == arnold_idx, arnold_house == i))
        solver.add(Implies(hair_vars[i-1] == red_idx, red_hair_house == i))
    
    solver.add(arnold_house < red_hair_house)
    
    # Clue 6: Alice is the person who loves swimming.
    alice_idx = names.index('Alice')
    swimming_idx = sports.index('swimming')
    for i in houses:
        solver.add(Implies(name_vars[i-1] == alice_idx, sport_vars[i-1] == swimming_idx))
    
    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    # This means red hair is in house N, black hair is in house N+1
    for i in range(3):  # houses 1-3 (since house 4 can't have someone directly to the right)
        solver.add(Implies(hair_vars[i] == red_idx, hair_vars[i+1] == black_idx))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in houses:
            idx = house - 1
            name_val = model.evaluate(name_vars[idx])
            hair_val = model.evaluate(hair_vars[idx])
            sport_val = model.evaluate(sport_vars[idx])
            
            # Convert to actual string values
            name_str = names[name_val.as_long()]
            hair_str = hair_colors[hair_val.as_long()]
            sport_str = sports[sport_val.as_long()]
            
            solution_data["solution"]["rows"].append([
                str(house),
                name_str,
                hair_str,
                sport_str
            ])
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()