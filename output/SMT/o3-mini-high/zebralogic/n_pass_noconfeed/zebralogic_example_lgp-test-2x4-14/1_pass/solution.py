import json
from z3 import *

def main():
    solver = Solver()
    num_houses = 2

    # Create variables for each attribute per house (houses indexed 0 to num_houses-1)
    names = [Int(f"name_{i}") for i in range(num_houses)]
    houseStyles = [Int(f"houseStyle_{i}") for i in range(num_houses)]
    smoothies = [Int(f"smoothie_{i}") for i in range(num_houses)]
    pets = [Int(f"pet_{i}") for i in range(num_houses)]

    # Domain: 0 or 1
    for var in names + houseStyles + smoothies + pets:
        solver.add(Or(var == 0, var == 1))

    # All-different constraints for each attribute type
    solver.add(Distinct(names))
    solver.add(Distinct(houseStyles))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(pets))

    # Mapping:
    # Names: 0 -> Eric,    1 -> Arnold
    # HouseStyle: 0 -> victorian, 1 -> colonial
    # Smoothie: 0 -> cherry,  1 -> desert
    # Pet: 0 -> dog,  1 -> cat

    # Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
    # For each house: smoothie==0 if and only if pet==0.
    for i in range(num_houses):
        solver.add(Or(And(smoothies[i] == 0, pets[i] == 0),
                      And(smoothies[i] == 1, pets[i] == 1)))

    # Clue 2: The person residing in a Victorian house is the person who owns a dog.
    # For each house: houseStyle==0 if and only if pet==0.
    for i in range(num_houses):
        solver.add(Or(And(houseStyles[i] == 0, pets[i] == 0),
                      And(houseStyles[i] == 1, pets[i] == 1)))

    # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
    # For every pair of houses, if a house is Victorian (houseStyle==0)
    # and another house has Eric (name==0), then the index of the Victorian house must be less.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(houseStyles[i] == 0, names[j] == 0), i < j))
    
    if solver.check() == sat:
        model = solver.model()

        # Define mapping dictionaries for output
        name_map = {0: "Eric", 1: "Arnold"}
        house_style_map = {0: "victorian", 1: "colonial"}
        smoothie_map = {0: "cherry", 1: "desert"}
        pet_map = {0: "dog", 1: "cat"}
        
        rows = []
        for i in range(num_houses):
            house_num = str(i + 1)
            name_val = model.evaluate(names[i]).as_long()
            style_val = model.evaluate(houseStyles[i]).as_long()
            smoothie_val = model.evaluate(smoothies[i]).as_long()
            pet_val = model.evaluate(pets[i]).as_long()
            
            row = [
                house_num,
                name_map[name_val],
                house_style_map[style_val],
                smoothie_map[smoothie_val],
                pet_map[pet_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()