import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    educations = ['associate', 'high school']
    
    # Create variables for each attribute per house
    name_vars = {h: z3.Int(f'name_{h}') for h in houses}
    style_vars = {h: z3.Int(f'style_{h}') for h in houses}
    height_vars = {h: z3.Int(f'height_{h}') for h in houses}
    education_vars = {h: z3.Int(f'education_{h}') for h in houses}
    
    # Define domains for each attribute
    name_domain = {0: 'Eric', 1: 'Arnold'}
    style_domain = {0: 'victorian', 1: 'colonial'}
    height_domain = {0: 'very short', 1: 'short'}
    education_domain = {0: 'associate', 1: 'high school'}
    
    # Constraint: All attributes must be within their domain
    for h in houses:
        solver.add(z3.And(name_vars[h] >= 0, name_vars[h] < len(names)))
        solver.add(z3.And(style_vars[h] >= 0, style_vars[h] < len(house_styles)))
        solver.add(z3.And(height_vars[h] >= 0, height_vars[h] < len(heights)))
        solver.add(z3.And(education_vars[h] >= 0, education_vars[h] < len(educations)))
    
    # Constraint: All attributes must be unique per house
    solver.add(z3.Distinct([name_vars[h] for h in houses]))
    solver.add(z3.Distinct([style_vars[h] for h in houses]))
    solver.add(z3.Distinct([height_vars[h] for h in houses]))
    solver.add(z3.Distinct([education_vars[h] for h in houses]))
    
    # Clue 1: The person who is short is directly left of Eric.
    # Since there are only 2 houses, short must be in house 1 and Eric in house 2
    solver.add(height_vars[1] == 1)  # short is in house 1
    solver.add(name_vars[2] == 0)    # Eric is in house 2
    
    # Clue 2: The person residing in a Victorian house is in the first house.
    solver.add(style_vars[1] == 0)  # victorian is in house 1
    
    # Clue 3: The person who is short is the person with an associate's degree.
    # Since short is in house 1, associate must also be in house 1
    solver.add(education_vars[1] == 0)  # associate is in house 1
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the solution
        header = ["House", "Name", "HouseStyle", "Height", "Education"]
        rows = []
        
        for house in sorted(houses):
            name_val = name_domain[model.evaluate(name_vars[house]).as_long()]
            style_val = style_domain[model.evaluate(style_vars[house]).as_long()]
            height_val = height_domain[model.evaluate(height_vars[house]).as_long()]
            education_val = education_domain[model.evaluate(education_vars[house]).as_long()]
            
            rows.append([str(house), name_val, style_val, height_val, education_val])
        
        # Create JSON output
        output = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()