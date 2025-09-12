import z3
import json

def main():
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    
    # Create variables for each attribute per house
    name_vars = {house: z3.Int(f'name_{house}') for house in houses}
    style_vars = {house: z3.Int(f'style_{house}') for house in houses}
    
    # Create mapping from integers to attribute values
    name_map = {i: name for i, name in enumerate(names)}
    style_map = {i: style for i, style in enumerate(house_styles)}
    
    # Constraint: All names are unique and within valid range
    for house in houses:
        solver.add(z3.And(name_vars[house] >= 0, name_vars[house] < len(names)))
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    
    # Constraint: All house styles are unique and within valid range
    for house in houses:
        solver.add(z3.And(style_vars[house] >= 0, style_vars[house] < len(house_styles)))
    solver.add(z3.Distinct([style_vars[house] for house in houses]))
    
    # Clue 1: Victorian house is to the left of colonial house
    # Find which house has victorian and which has colonial
    victorian_index = house_styles.index('victorian')
    colonial_index = house_styles.index('colonial')
    
    # Victorian house must have lower house number than colonial house
    for house1 in houses:
        for house2 in houses:
            if house1 < house2:
                # If house1 has victorian, then house2 cannot have colonial if house1 < house2
                # But we need to express: victorian is left of colonial
                # So we add constraint that if a house has victorian, then some house to its right must have colonial
                pass
    
    # Better approach: find the house with victorian and the house with colonial
    # and ensure victorian house number < colonial house number
    victorian_house = z3.Int('victorian_house')
    colonial_house = z3.Int('colonial_house')
    
    solver.add(victorian_house >= 1, victorian_house <= 2)
    solver.add(colonial_house >= 1, colonial_house <= 2)
    solver.add(victorian_house != colonial_house)
    
    # Link these variables to the style variables
    for house in houses:
        solver.add(z3.Implies(style_vars[house] == victorian_index, victorian_house == house))
        solver.add(z3.Implies(style_vars[house] == colonial_index, colonial_house == house))
    
    solver.add(victorian_house < colonial_house)
    
    # Clue 2: Eric is in the first house
    eric_index = names.index('Eric')
    solver.add(name_vars[1] == eric_index)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        rows = []
        for house in sorted(houses):
            name_val = model.eval(name_vars[house]).as_long()
            style_val = model.eval(style_vars[house]).as_long()
            
            rows.append([
                str(house),
                name_map[name_val],
                style_map[style_val]
            ])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()