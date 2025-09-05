#!/usr/bin/env python
import json
from z3 import *

def main():
    s = Solver()
    
    # Create integer variables for each house's features.
    # We'll use:
    # For Name: 0 = Eric, 1 = Arnold
    # For HouseStyle: 0 = victorian, 1 = colonial
    # For Height: 0 = very short, 1 = short
    # For Education: 0 = associate, 1 = high school
    house1_name = Int('house1_name')
    house2_name = Int('house2_name')
    
    house1_style = Int('house1_style')
    house2_style = Int('house2_style')
    
    house1_height = Int('house1_height')
    house2_height = Int('house2_height')
    
    house1_education = Int('house1_education')
    house2_education = Int('house2_education')
    
    # Domain constraints: each variable is either 0 or 1.
    s.add(Or(house1_name == 0, house1_name == 1))
    s.add(Or(house2_name == 0, house2_name == 1))
    
    s.add(Or(house1_style == 0, house1_style == 1))
    s.add(Or(house2_style == 0, house2_style == 1))
    
    s.add(Or(house1_height == 0, house1_height == 1))
    s.add(Or(house2_height == 0, house2_height == 1))
    
    s.add(Or(house1_education == 0, house1_education == 1))
    s.add(Or(house2_education == 0, house2_education == 1))
    
    # All features must be unique across houses.
    s.add(Distinct(house1_name, house2_name))
    s.add(Distinct(house1_style, house2_style))
    s.add(Distinct(house1_height, house2_height))
    s.add(Distinct(house1_education, house2_education))
    
    # Clue 2: The person residing in a Victorian house is in the first house.
    # Victorian is encoded as 0.
    s.add(house1_style == 0)
    
    # Clue 1: The person who is short is directly left of Eric.
    # With 2 houses, this forces house1 to be short and house2 to be Eric.
    s.add(house1_height == 1)   # short is encoded as 1
    s.add(house2_name == 0)     # Eric is encoded as 0
    
    # Clue 3: The person who is short is the person with an associate's degree.
    # In our encoding, associate is 0. Apply the rule for both houses.
    s.add(Implies(house1_height == 1, house1_education == 0))
    s.add(Implies(house2_height == 1, house2_education == 0))
    
    if s.check() == sat:
        m = s.model()
        # Define mapping from integer codes to attribute names.
        name_mapping = {0: "Eric", 1: "Arnold"}
        style_mapping = {0: "victorian", 1: "colonial"}
        height_mapping = {0: "very short", 1: "short"}
        education_mapping = {0: "associate", 1: "high school"}
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": [
                    [
                        "1",
                        name_mapping[m[house1_name].as_long()],
                        style_mapping[m[house1_style].as_long()],
                        height_mapping[m[house1_height].as_long()],
                        education_mapping[m[house1_education].as_long()]
                    ],
                    [
                        "2",
                        name_mapping[m[house2_name].as_long()],
                        style_mapping[m[house2_style].as_long()],
                        height_mapping[m[house2_height].as_long()],
                        education_mapping[m[house2_education].as_long()]
                    ]
                ]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()