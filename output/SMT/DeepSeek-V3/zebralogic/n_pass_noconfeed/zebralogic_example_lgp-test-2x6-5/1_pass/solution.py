import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define attributes
    houses = [1, 2]
    names = ['Arnold', 'Eric']
    occupations = ['engineer', 'doctor']
    birthdays = ['april', 'sept']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    cigars = ['pall mall', 'prince']
    
    # Create variables for each attribute per house
    name_vars = {house: z3.Int(f'name_{house}') for house in houses}
    occupation_vars = {house: z3.Int(f'occupation_{house}') for house in houses}
    birthday_vars = {house: z3.Int(f'birthday_{house}') for house in houses}
    house_style_vars = {house: z3.Int(f'house_style_{house}') for house in houses}
    height_vars = {house: z3.Int(f'height_{house}') for house in houses}
    cigar_vars = {house: z3.Int(f'cigar_{house}') for house in houses}
    
    # Define domains for each attribute
    name_domain = {0: 'Arnold', 1: 'Eric'}
    occupation_domain = {0: 'engineer', 1: 'doctor'}
    birthday_domain = {0: 'april', 1: 'sept'}
    house_style_domain = {0: 'victorian', 1: 'colonial'}
    height_domain = {0: 'very short', 1: 'short'}
    cigar_domain = {0: 'pall mall', 1: 'prince'}
    
    # Constraint: All attributes within valid range
    for house in houses:
        solver.add(z3.And(name_vars[house] >= 0, name_vars[house] < len(names)))
        solver.add(z3.And(occupation_vars[house] >= 0, occupation_vars[house] < len(occupations)))
        solver.add(z3.And(birthday_vars[house] >= 0, birthday_vars[house] < len(birthdays)))
        solver.add(z3.And(house_style_vars[house] >= 0, house_style_vars[house] < len(house_styles)))
        solver.add(z3.And(height_vars[house] >= 0, height_vars[house] < len(heights)))
        solver.add(z3.And(cigar_vars[house] >= 0, cigar_vars[house] < len(cigars)))
    
    # Constraint: All attributes are unique within their category
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    solver.add(z3.Distinct([occupation_vars[house] for house in houses]))
    solver.add(z3.Distinct([birthday_vars[house] for house in houses]))
    solver.add(z3.Distinct([house_style_vars[house] for house in houses]))
    solver.add(z3.Distinct([height_vars[house] for house in houses]))
    solver.add(z3.Distinct([cigar_vars[house] for house in houses]))
    
    # Clue 1: The person who is an engineer is in the first house.
    solver.add(occupation_vars[1] == 0)  # engineer is index 0
    
    # Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
    # Since there are only 2 houses, they are always adjacent
    # This clue is automatically satisfied with 2 houses
    
    # Clue 3: The person living in a colonial-style house is the person who is an engineer.
    for house in houses:
        solver.add(z3.Implies(house_style_vars[house] == 1, occupation_vars[house] == 0))
    
    # Clue 4: The person who is very short is the person who is an engineer.
    for house in houses:
        solver.add(z3.Implies(height_vars[house] == 0, occupation_vars[house] == 0))
    
    # Clue 5: The person who is short is the person partial to Pall Mall.
    for house in houses:
        solver.add(z3.Implies(height_vars[house] == 1, cigar_vars[house] == 0))
    
    # Clue 6: The person who is an engineer is Eric.
    for house in houses:
        solver.add(z3.Implies(occupation_vars[house] == 0, name_vars[house] == 1))
    
    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": []
            }
        }
        
        for house in sorted(houses):
            name_val = model.evaluate(name_vars[house]).as_long()
            occupation_val = model.evaluate(occupation_vars[house]).as_long()
            birthday_val = model.evaluate(birthday_vars[house]).as_long()
            house_style_val = model.evaluate(house_style_vars[house]).as_long()
            height_val = model.evaluate(height_vars[house]).as_long()
            cigar_val = model.evaluate(cigar_vars[house]).as_long()
            
            row = [
                str(house),
                name_domain[name_val],
                occupation_domain[occupation_val],
                birthday_domain[birthday_val],
                house_style_domain[house_style_val],
                height_domain[height_val],
                cigar_domain[cigar_val]
            ]
            solution["solution"]["rows"].append(row)
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()