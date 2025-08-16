import json
from z3 import *

def solve_puzzle():
    # Create the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]
    
    # Define the attributes
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["craftsman", "colonial", "victorian", "ranch"]
    hair_colors = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    genres = ["mystery", "fantasy", "romance", "science fiction"]

    # Create variables for each attribute in each house
    name = {h: Const(f'name_{h}', StringSort()) for h in houses}
    style = {h: Const(f'style_{h}', StringSort()) for h in houses}
    hair = {h: Const(f'hair_{h}', StringSort()) for h in houses}
    child = {h: Const(f'child_{h}', StringSort()) for h in houses}
    genre = {h: Const(f'genre_{h}', StringSort()) for h in houses}

    # Add constraints that each attribute must be one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([style[h] == s for s in styles]))
        s.add(Or([hair[h] == c for c in hair_colors]))
        s.add(Or([child[h] == c for c in children]))
        s.add(Or([genre[h] == g for g in genres]))

    # Add uniqueness constraints for each attribute
    for attr in [name, style, hair, child, genre]:
        for i in houses:
            for j in houses:
                if i < j:
                    s.add(attr[i] != attr[j])

    # Add the clues as constraints
    # 1. The person in a Craftsman-style house is in the third house.
    s.add(style[3] == "craftsman")
    
    # 2. Alice is the person who loves romance books.
    for h in houses:
        s.add(Implies(name[h] == "Alice", genre[h] == "romance"))
    
    # 3. The person who has brown hair is in the fourth house.
    s.add(hair[4] == "brown")
    
    # 4. The person's child is named Samantha is in the fourth house.
    s.add(child[4] == "Samantha")
    
    # 5. The person in a ranch-style home is somewhere to the right of the person who has red hair.
    # First find the house with red hair, then ranch must be to its right
    red_hair_house = Int('red_hair_house')
    s.add(Or([And(hair[h] == "red", red_hair_house == h) for h in houses]))
    ranch_house = Int('ranch_house')
    s.add(Or([And(style[h] == "ranch", ranch_house == h) for h in houses]))
    s.add(ranch_house > red_hair_house)
    
    # 6. Peter is the person's child is named Bella.
    for h in houses:
        s.add(Implies(name[h] == "Peter", child[h] == "Bella"))
    
    # 7. Arnold is the person who has red hair.
    for h in houses:
        s.add(Implies(name[h] == "Arnold", hair[h] == "red"))
    
    # 8. Alice is the person living in a colonial-style house.
    for h in houses:
        s.add(Implies(name[h] == "Alice", style[h] == "colonial"))
    
    # 9. The person who has black hair is in the second house.
    s.add(hair[2] == "black")
    
    # 10. The person who loves fantasy books is Peter.
    for h in houses:
        s.add(Implies(name[h] == "Peter", genre[h] == "fantasy"))
    
    # 11. Arnold is the person's child is named Meredith.
    for h in houses:
        s.add(Implies(name[h] == "Arnold", child[h] == "Meredith"))
    
    # 12. The person who has black hair is Eric.
    for h in houses:
        s.add(Implies(hair[h] == "black", name[h] == "Eric"))
    
    # 13. The person who loves science fiction books is Arnold.
    for h in houses:
        s.add(Implies(name[h] == "Arnold", genre[h] == "science fiction"))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": []
            }
        }
        
        # Collect the values for each house
        for h in sorted(houses):
            row = [
                str(h),
                str(model.eval(name[h])),
                str(model.eval(style[h])),
                str(model.eval(hair[h])),
                str(model.eval(child[h])),
                str(model.eval(genre[h]))
            ]
            solution["solution"]["rows"].append(row)
        
        return solution
    else:
        return {"error": "No solution found"}

# Solve the puzzle and print the JSON result
result = solve_puzzle()
print(json.dumps(result, indent=2))