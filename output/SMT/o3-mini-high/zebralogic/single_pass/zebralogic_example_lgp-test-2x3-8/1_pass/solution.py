from z3 import Int, Solver, And, Distinct
import json

def main():
    solver = Solver()

    # Create integer variables representing the house number (1 or 2) assigned to each attribute.
    # For names:
    house_Eric   = Int('house_Eric')
    house_Arnold = Int('house_Arnold')
    
    # For birthdays:
    house_april = Int('house_april')
    house_sept  = Int('house_sept')
    
    # For mothers:
    house_Aniya = Int('house_Aniya')
    house_Holly = Int('house_Holly')
    
    # Each house number must be either 1 or 2:
    solver.add(And(house_Eric >= 1, house_Eric <= 2))
    solver.add(And(house_Arnold >= 1, house_Arnold <= 2))
    solver.add(And(house_april >= 1, house_april <= 2))
    solver.add(And(house_sept  >= 1, house_sept  <= 2))
    solver.add(And(house_Aniya >= 1, house_Aniya <= 2))
    solver.add(And(house_Holly >= 1, house_Holly <= 2))
    
    # The two persons must live in different houses.
    solver.add(Distinct(house_Eric, house_Arnold))
    
    # The two birthdays must be in different houses.
    solver.add(Distinct(house_april, house_sept))
    
    # The two mothers must be in different houses.
    solver.add(Distinct(house_Aniya, house_Holly))
    
    # Clue 2: The person whose birthday is in April is in the first house.
    solver.add(house_april == 1)
    
    # Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
    # Since houses are numbered from left (1) to right (2), this means:
    solver.add(house_Eric < house_Holly)
    
    # Check for satisfiability.
    if solver.check() == 'sat' or solver.check() == 1:
        model = solver.model()
        
        # Create a mapping for houses with placeholders for each attribute.
        houses = {
            1: {"Name": None, "Birthday": None, "Mother": None},
            2: {"Name": None, "Birthday": None, "Mother": None}
        }
        
        # Assign names:
        house_num = model.evaluate(house_Eric).as_long()
        houses[house_num]["Name"] = "Eric"
        
        house_num = model.evaluate(house_Arnold).as_long()
        houses[house_num]["Name"] = "Arnold"
        
        # Assign birthdays:
        house_num = model.evaluate(house_april).as_long()
        houses[house_num]["Birthday"] = "april"
        
        house_num = model.evaluate(house_sept).as_long()
        houses[house_num]["Birthday"] = "sept"
        
        # Assign mothers:
        house_num = model.evaluate(house_Aniya).as_long()
        houses[house_num]["Mother"] = "Aniya"
        
        house_num = model.evaluate(house_Holly).as_long()
        houses[house_num]["Mother"] = "Holly"
        
        # Prepare the final JSON output in the required structure.
        solution_output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": [
                    [ "1",
                      houses[1]["Name"],
                      houses[1]["Birthday"],
                      houses[1]["Mother"]
                    ],
                    [ "2",
                      houses[2]["Name"],
                      houses[2]["Birthday"],
                      houses[2]["Mother"]
                    ]
                ]
            }
        }
        print(json.dumps(solution_output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()