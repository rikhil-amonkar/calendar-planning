import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Eric', 'Arnold']
    sports = ['basketball', 'soccer']
    hobbies = ['photography', 'gardening']
    
    # Create variables for each attribute per house
    name_vars = {}
    sport_vars = {}
    hobby_vars = {}
    
    for house in houses:
        name_vars[house] = z3.Int(f'name_{house}')
        sport_vars[house] = z3.Int(f'sport_{house}')
        hobby_vars[house] = z3.Int(f'hobby_{house}')
    
    # Constraint: All attributes are distinct within their category
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    solver.add(z3.Distinct([sport_vars[house] for house in houses]))
    solver.add(z3.Distinct([hobby_vars[house] for house in houses]))
    
    # Constraint: All values are within valid range (0-1 for 2 options)
    for house in houses:
        solver.add(name_vars[house] >= 0, name_vars[house] < len(names))
        solver.add(sport_vars[house] >= 0, sport_vars[house] < len(sports))
        solver.add(hobby_vars[house] >= 0, hobby_vars[house] < len(hobbies))
    
    # Clue 1: The person who enjoys gardening is Arnold.
    # Arnold is at index 1, gardening is at index 1
    for house in houses:
        solver.add(z3.Implies(hobby_vars[house] == 1, name_vars[house] == 1))
    
    # Clue 2: The photography enthusiast is not in the first house.
    # Photography is at index 0
    solver.add(hobby_vars[1] != 0)
    
    # Clue 3: The person who loves soccer is not in the first house.
    # Soccer is at index 1
    solver.add(sport_vars[1] != 1)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare result structure
        result = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in sorted(houses):
            name_idx = model.evaluate(name_vars[house]).as_long()
            sport_idx = model.evaluate(sport_vars[house]).as_long()
            hobby_idx = model.evaluate(hobby_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                sports[sport_idx],
                hobbies[hobby_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()