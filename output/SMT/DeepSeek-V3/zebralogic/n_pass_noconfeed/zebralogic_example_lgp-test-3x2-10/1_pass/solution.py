import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Create variables for names and heights
    name_vars = {house: z3.Int(f'name_{house}') for house in houses}
    height_vars = {house: z3.Int(f'height_{house}') for house in houses}
    
    # Define domains for names and heights
    names = ['Eric', 'Arnold', 'Peter']
    name_domain = {name: idx for idx, name in enumerate(names)}
    
    heights = ['very short', 'short', 'average']
    height_domain = {height: idx for idx, height in enumerate(heights)}
    
    # Constraint: All names are different and within domain
    for house in houses:
        solver.add(z3.And(name_vars[house] >= 0, name_vars[house] < len(names)))
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    
    # Constraint: All heights are different and within domain
    for house in houses:
        solver.add(z3.And(height_vars[house] >= 0, height_vars[house] < len(heights)))
    solver.add(z3.Distinct([height_vars[house] for house in houses]))
    
    # Clue 1: Eric is not in the first house
    solver.add(name_vars[1] != name_domain['Eric'])
    
    # Clue 2: The person who is very short is somewhere to the left of the person who is short
    very_short_house = z3.Int('very_short_house')
    short_house = z3.Int('short_house')
    
    # Find which house has very short height
    for house in houses:
        solver.add(z3.Implies(height_vars[house] == height_domain['very short'], very_short_house == house))
    
    # Find which house has short height
    for house in houses:
        solver.add(z3.Implies(height_vars[house] == height_domain['short'], short_house == house))
    
    # Very short is to the left of short
    solver.add(very_short_house < short_house)
    
    # Clue 3: The person who is very short is Eric
    for house in houses:
        solver.add(z3.Implies(height_vars[house] == height_domain['very short'], 
                             name_vars[house] == name_domain['Eric']))
    
    # Clue 4: Arnold is not in the first house
    solver.add(name_vars[1] != name_domain['Arnold'])
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in sorted(houses):
            name_val = model.eval(name_vars[house]).as_long()
            height_val = model.eval(height_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_val],
                heights[height_val]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()