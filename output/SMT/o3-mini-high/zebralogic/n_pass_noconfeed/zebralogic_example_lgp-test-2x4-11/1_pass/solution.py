from z3 import *
import json

def main():
    solver = Solver()
    n = 2  # There are 2 houses, indexed 0 and 1 corresponding to houses 1 and 2

    # Define variables for each house.
    # For Name: 0 -> "Eric", 1 -> "Arnold"
    names = [Int(f"name_{i}") for i in range(n)]
    # For Hobby: 0 -> "photography", 1 -> "gardening"
    hobbies = [Int(f"hobby_{i}") for i in range(n)]
    # For Pet: 0 -> "cat", 1 -> "dog"
    pets = [Int(f"pet_{i}") for i in range(n)]
    # For Height: 0 -> "very short", 1 -> "short"
    heights = [Int(f"height_{i}") for i in range(n)]
    
    # Domain constraints: each variable must be either 0 or 1.
    for i in range(n):
        solver.add(Or(names[i] == 0, names[i] == 1))
        solver.add(Or(hobbies[i] == 0, hobbies[i] == 1))
        solver.add(Or(pets[i] == 0, pets[i] == 1))
        solver.add(Or(heights[i] == 0, heights[i] == 1))
    
    # All attributes are unique across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(hobbies))
    solver.add(Distinct(pets))
    solver.add(Distinct(heights))
    
    # Clue 3: "The person who has a cat is somewhere to the right of the person who is very short."
    # With only 2 houses (indexes 0 and 1) the only possibility is:
    # - The house at index 0 (leftmost / house 1) must be "very short"
    # - The house at index 1 (right of house 1) must have a cat.
    solver.add(heights[0] == 0)
    solver.add(pets[1] == 0)
    
    # Clue 1: "The person who is very short is the photography enthusiast."
    # For each house, if height is very short (0) then hobby must be photography (0).
    for i in range(n):
        solver.add(Implies(heights[i] == 0, hobbies[i] == 0))
    
    # Clue 2: "Eric is the person who is very short."
    # For each house, if the person is Eric (name 0) then their height must be very short (0).
    for i in range(n):
        solver.add(Implies(names[i] == 0, heights[i] == 0))
    
    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()

        # Mapping integers back to attribute strings.
        name_map = {0: "Eric", 1: "Arnold"}
        hobby_map = {0: "photography", 1: "gardening"}
        pet_map = {0: "cat", 1: "dog"}
        height_map = {0: "very short", 1: "short"}
        
        solution_rows = []
        # Houses are ordered from left to right: index 0 corresponds to House "1" and index 1 to House "2".
        for i in range(n):
            house_number = str(i + 1)
            name_val = name_map[model.evaluate(names[i]).as_long()]
            hobby_val = hobby_map[model.evaluate(hobbies[i]).as_long()]
            pet_val = pet_map[model.evaluate(pets[i]).as_long()]
            height_val = height_map[model.evaluate(heights[i]).as_long()]
            solution_rows.append([house_number, name_val, hobby_val, pet_val, height_val])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        # If no solution exists, output an empty rows list.
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": []
            }
        }
        print(json.dumps(result))

if __name__ == "__main__":
    main()