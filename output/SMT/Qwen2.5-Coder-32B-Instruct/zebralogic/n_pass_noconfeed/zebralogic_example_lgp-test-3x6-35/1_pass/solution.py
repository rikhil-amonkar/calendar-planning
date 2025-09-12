from z3 import *

# Define the variables
names = ['Eric', 'Arnold', 'Peter']
vacations = ['mountain', 'city', 'beach']
heights = ['very short', 'average', 'short']
flowers = ['carnations', 'daffodils', 'lilies']
hair_colors = ['brown', 'black', 'blonde']
educations = ['associate', 'bachelor', 'high school']

# Create dictionaries to hold the Z3 variables
name_vars = {name: Int(f'{name}_house') for name in names}
vacation_vars = {vacation: Int(f'{vacation}_house') for vacation in vacations}
height_vars = {height: Int(f'{height}_house') for height in heights}
flower_vars = {flower: Int(f'{flower}_house') for flower in flowers}
hair_color_vars = {hair_color: Int(f'{hair_color}_house') for hair_color in hair_colors}
education_vars = {education: Int(f'{education}_house') for education in educations}

# Create a solver instance
solver = Solver()

# Add constraints for each variable to be between 1 and 3
for var_dict in [name_vars, vacation_vars, height_vars, flower_vars, hair_color_vars, education_vars]:
    for var in var_dict.values():
        solver.add(And(var >= 1, var <= 3))

# Add constraints for all variables to be distinct
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(vacation_vars.values())))
solver.add(Distinct(list(height_vars.values())))
solver.add(Distinct(list(flower_vars.values())))
solver.add(Distinct(list(hair_color_vars.values())))
solver.add(Distinct(list(education_vars.values())))

# Add specific clues as constraints
solver.add(name_vars['Peter'] == height_vars['average'])
solver.add(flower_vars['daffodils'] == name_vars['Arnold'])
solver.add(height_vars['very short'] != 2)
solver.add(vacation_vars['beach'] == 1)
solver.add(education_vars['high school'] == 3)
solver.add(height_vars['short'] > height_vars['very short'])
solver.add(flower_vars['lilies'] == name_vars['Eric'])
solver.add(flower_vars['lilies'] == education_vars['bachelor'])
solver.add(vacation_vars['city'] > name_vars['Peter'])
solver.add(hair_color_vars['blonde'] == 3)
solver.add(vacation_vars['beach'] == hair_color_vars['brown'])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": []
        }
    }
    
    for house in range(1, 4):
        row = [str(house)]
        for attr, var_dict in zip(["Name", "Vacation", "Height", "Flower", "HairColor", "Education"], 
                                 [name_vars, vacation_vars, height_vars, flower_vars, hair_color_vars, education_vars]):
            for key, value in var_dict.items():
                if model.evaluate(value) == house:
                    row.append(key)
                    break
        solution["solution"]["rows"].append(row)
    
    import json
    print(json.dumps(solution))
else:
    print("No solution found")