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
    
    # Create Z3 variables for each house and attribute
    house1_name = Int('house1_name')
    house1_style = Int('house1_style')
    house1_height = Int('house1_height')
    house1_education = Int('house1_education')
    
    house2_name = Int('house2_name')
    house2_style = Int('house2_style')
    house2_height = Int('house2_height')
    house2_education = Int('house2_education')
    
    # Constrain all attributes to be within their domains (0-1 for all since 2 values each)
    solver.add(house1_name >= 0, house1_name < 2)
    solver.add(house1_style >= 0, house1_style < 2)
    solver.add(house1_height >= 0, house1_height < 2)
    solver.add(house1_education >= 0, house1_education < 2)
    
    solver.add(house2_name >= 0, house2_name < 2)
    solver.add(house2_style >= 0, house2_style < 2)
    solver.add(house2_height >= 0, house2_height < 2)
    solver.add(house2_education >= 0, house2_education < 2)
    
    # All attributes must be different within their category
    solver.add(Distinct(house1_name, house2_name))
    solver.add(Distinct(house1_style, house2_style))
    solver.add(Distinct(house1_height, house2_height))
    solver.add(Distinct(house1_education, house2_education))
    
    # Clue 1: The person who is short is directly left of Eric
    # Meaning: Short height in house 1, Eric in house 2
    solver.add(house1_height == heights.index('short'))
    solver.add(house2_name == names.index('Eric'))
    
    # Clue 2: Victorian house is in first house
    solver.add(house1_style == styles.index('victorian'))
    
    # Clue 3: Short height person has associate degree
    # Since short is in house 1 (from clue 1), so house1 has associate
    solver.add(house1_education == educations.index('associate'))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Map integer values back to their string representations
        attributes = [
            [
                "1",
                names[model[house1_name].as_long()],
                styles[model[house1_style].as_long()],
                heights[model[house1_height].as_long()],
                educations[model[house1_education].as_long()]
            ],
            [
                "2",
                names[model[house2_name].as_long()],
                styles[model[house2_style].as_long()],
                heights[model[house2_height].as_long()],
                educations[model[house2_education].as_long()]
            ]
        ]
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": attributes
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()