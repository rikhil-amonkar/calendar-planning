from z3 import *
import json

def main():
    # Define the enums for each attribute
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name = Name.create()
    
    Mother = Datatype('Mother')
    Mother.declare('Aniya')
    Mother.declare('Holly')
    Mother = Mother.create()
    
    CarModel = Datatype('CarModel')
    CarModel.declare('ford_f150')
    CarModel.declare('tesla_model_3')
    CarModel = CarModel.create()
    
    Height = Datatype('Height')
    Height.declare('short')
    Height.declare('very_short')
    Height = Height.create()
    
    # Create variables for house 1 and house 2
    house1_name = Const('house1_name', Name)
    house1_mother = Const('house1_mother', Mother)
    house1_car = Const('house1_car', CarModel)
    house1_height = Const('house1_height', Height)
    
    house2_name = Const('house2_name', Name)
    house2_mother = Const('house2_mother', Mother)
    house2_car = Const('house2_car', CarModel)
    house2_height = Const('house2_height', Height)
    
    s = Solver()
    
    # All attributes must be distinct per category
    s.add(Distinct(house1_name, house2_name))
    s.add(Distinct(house1_mother, house2_mother))
    s.add(Distinct(house1_car, house2_car))
    s.add(Distinct(house1_height, house2_height))
    
    # Clue 1: Tesla owner is to the right of Arnold -> Arnold must be in house 1, Tesla in house 2
    s.add(house1_name == Name.Arnold)
    s.add(house2_car == CarModel.tesla_model_3)
    
    # Clue 2: Arnold is short
    s.add(house1_height == Height.short)
    
    # Clue 3: Mother Holly is in house 2
    s.add(house2_mother == Mother.Holly)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        
        # Helper functions to convert Z3 enum to string
        def name_str(val):
            if eq(val, Name.Eric):
                return "Eric"
            elif eq(val, Name.Arnold):
                return "Arnold"
            else:
                return str(val)
        
        def mother_str(val):
            if eq(val, Mother.Aniya):
                return "Aniya"
            elif eq(val, Mother.Holly):
                return "Holly"
            else:
                return str(val)
        
        def car_str(val):
            if eq(val, CarModel.ford_f150):
                return "ford f150"
            elif eq(val, CarModel.tesla_model_3):
                return "tesla model 3"
            else:
                return str(val)
        
        def height_str(val):
            if eq(val, Height.short):
                return "short"
            elif eq(val, Height.very_short):
                return "very short"
            else:
                return str(val)
        
        # Extract values for house 1
        h1_name = name_str(m[house1_name])
        h1_mother = mother_str(m[house1_mother])
        h1_car = car_str(m[house1_car])
        h1_height = height_str(m[house1_height])
        
        # Extract values for house 2
        h2_name = name_str(m[house2_name])
        h2_mother = mother_str(m[house2_mother])
        h2_car = car_str(m[house2_car])
        h2_height = height_str(m[house2_height])
        
        # Build the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": [
                    ["1", h1_name, h1_mother, h1_car, h1_height],
                    ["2", h2_name, h2_mother, h2_car, h2_height]
                ]
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()