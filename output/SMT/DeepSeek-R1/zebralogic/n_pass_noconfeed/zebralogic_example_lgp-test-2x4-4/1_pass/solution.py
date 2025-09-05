import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define attributes
    names = ['Eric', 'Arnold']
    styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    educations = ['associate', 'high school']
    
    # Create enums for each attribute type
    Name = Datatype('Name')
    for n in names:
        Name.declare(n)
    Name = Name.create()
    
    Style = Datatype('Style')
    for s in styles:
        Style.declare(s)
    Style = Style.create()
    
    Height = Datatype('Height')
    for h in heights:
        Height.declare(h)
    Height = Height.create()
    
    Education = Datatype('Education')
    for e in educations:
        Education.declare(e)
    Education = Education.create()
    
    # Create variables for each house
    house1_name = Const('house1_name', Name)
    house1_style = Const('house1_style', Style)
    house1_height = Const('house1_height', Height)
    house1_education = Const('house1_education', Education)
    
    house2_name = Const('house2_name', Name)
    house2_style = Const('house2_style', Style)
    house2_height = Const('house2_height', Height)
    house2_education = Const('house2_education', Education)
    
    # All attributes must be unique within their category
    solver.add(Distinct(house1_name, house2_name))
    solver.add(Distinct(house1_style, house2_style))
    solver.add(Distinct(house1_height, house2_height))
    solver.add(Distinct(house1_education, house2_education))
    
    # Clue 1: The person who is short is directly left of Eric
    solver.add(house1_height == Height.short)
    solver.add(house2_name == Name.Eric)
    
    # Clue 2: The person residing in a Victorian house is in the first house
    solver.add(house1_style == Style.victorian)
    
    # Clue 3: The person who is short is the person with an associate's degree
    solver.add(house1_education == Education.associate)
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Function to get string value from Z3 symbol
        def get_value(symbol, model):
            return str(model[symbol]).split('!')[0]
        
        # Prepare solution data
        rows = []
        for i in range(1, 3):
            name_val = get_value(eval(f'house{i}_name'), model)
            style_val = get_value(eval(f'house{i}_style'), model)
            height_val = get_value(eval(f'house{i}_height'), model)
            education_val = get_value(eval(f'house{i}_education'), model)
            rows.append([str(i), name_val, style_val, height_val, education_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()