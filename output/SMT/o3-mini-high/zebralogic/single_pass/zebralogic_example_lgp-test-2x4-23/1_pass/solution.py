from z3 import *

def solve():
    s = Solver()

    # Create integer variables for each attribute in house 1 and house 2.
    # Domain for each variable is 0 or 1.
    # Mapping:
    #   Names:    0 -> "Arnold",   1 -> "Eric"
    #   Mothers:  0 -> "Aniya",    1 -> "Holly"
    #   Cars:     0 -> "ford f150", 1 -> "tesla model 3"
    #   Heights:  0 -> "short",     1 -> "very short"
    house1_name   = Int('house1_name')
    house2_name   = Int('house2_name')
    house1_mother = Int('house1_mother')
    house2_mother = Int('house2_mother')
    house1_car    = Int('house1_car')
    house2_car    = Int('house2_car')
    house1_height = Int('house1_height')
    house2_height = Int('house2_height')

    # Each variable is either 0 or 1.
    s.add(Or(house1_name == 0, house1_name == 1))
    s.add(Or(house2_name == 0, house2_name == 1))
    s.add(Or(house1_mother == 0, house1_mother == 1))
    s.add(Or(house2_mother == 0, house2_mother == 1))
    s.add(Or(house1_car == 0, house1_car == 1))
    s.add(Or(house2_car == 0, house2_car == 1))
    s.add(Or(house1_height == 0, house1_height == 1))
    s.add(Or(house2_height == 0, house2_height == 1))

    # All attributes are unique per category.
    s.add(Distinct(house1_name, house2_name))
    s.add(Distinct(house1_mother, house2_mother))
    s.add(Distinct(house1_car, house2_car))
    s.add(Distinct(house1_height, house2_height))

    # Clue 3: The person whose mother's name is Holly is in the second house.
    # Since Holly is mapped to 1, we have:
    s.add(house2_mother == 1)
    # By distinctness, house1_mother will be 0 ("Aniya").

    # Clue 2: Arnold is the person who is short.
    # Arnold is 0; short is 0.
    s.add(Implies(house1_name == 0, house1_height == 0))
    s.add(Implies(house2_name == 0, house2_height == 0))
    
    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    # "Right" implies a higher house number.
    # If Arnold (name 0) were in house2, there would be no house to the right.
    # Therefore, Arnold must be in house1, and Tesla (car value 1) must be in house2.
    s.add(house2_name != 0)
    s.add(house2_car == 1)
    # By distinctness, house1_car will then be 0 ("ford f150").

    # At this point, the only possible assignment is:
    # House 1: name = 0 ("Arnold"), mother = 0 ("Aniya"), car = 0 ("ford f150"), height = 0 ("short")
    # House 2: name = 1 ("Eric"),  mother = 1 ("Holly" ), car = 1 ("tesla model 3"), height = 1 ("very short")
    
    if s.check() == sat:
        m = s.model()

        # Create mapping dictionaries for final output.
        names   = {0: "Arnold", 1: "Eric"}
        mothers = {0: "Aniya", 1: "Holly"}
        cars    = {0: "ford f150", 1: "tesla model 3"}
        heights = {0: "short", 1: "very short"}

        house1_name_val   = m[house1_name].as_long()
        house1_mother_val = m[house1_mother].as_long()
        house1_car_val    = m[house1_car].as_long()
        house1_height_val = m[house1_height].as_long()

        house2_name_val   = m[house2_name].as_long()
        house2_mother_val = m[house2_mother].as_long()
        house2_car_val    = m[house2_car].as_long()
        house2_height_val = m[house2_height].as_long()

        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": [
                    ["1", names[house1_name_val], mothers[house1_mother_val], cars[house1_car_val], heights[house1_height_val]],
                    ["2", names[house2_name_val], mothers[house2_mother_val], cars[house2_car_val], heights[house2_height_val]]
                ]
            }
        }
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    solve()