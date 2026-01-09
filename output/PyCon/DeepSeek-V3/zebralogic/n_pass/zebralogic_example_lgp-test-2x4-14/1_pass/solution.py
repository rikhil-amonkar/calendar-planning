import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables for each attribute
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"style_{house}", styles)
        problem.addVariable(f"smoothie_{house}", smoothies)
        problem.addVariable(f"pet_{house}", pets)
    
    # All attributes must be unique across houses
    problem.addConstraint(lambda n1, n2: n1 != n2, 
                         [f"name_{house}" for house in houses])
    problem.addConstraint(lambda s1, s2: s1 != s2, 
                         [f"style_{house}" for house in houses])
    problem.addConstraint(lambda sm1, sm2: sm1 != sm2, 
                         [f"smoothie_{house}" for house in houses])
    problem.addConstraint(lambda p1, p2: p1 != p2, 
                         [f"pet_{house}" for house in houses])
    
    # Clue 1: The person who likes Cherry smoothies is the person who owns a dog
    for house in houses:
        problem.addConstraint(
            lambda smoothie, pet: not (smoothie == "cherry") or (pet == "dog"),
            [f"smoothie_{house}", f"pet_{house}"]
        )
        problem.addConstraint(
            lambda smoothie, pet: not (pet == "dog") or (smoothie == "cherry"),
            [f"smoothie_{house}", f"pet_{house}"]
        )
    
    # Clue 2: The person residing in a Victorian house is the person who owns a dog
    for house in houses:
        problem.addConstraint(
            lambda style, pet: not (style == "victorian") or (pet == "dog"),
            [f"style_{house}", f"pet_{house}"]
        )
        problem.addConstraint(
            lambda style, pet: not (pet == "dog") or (style == "victorian"),
            [f"style_{house}", f"pet_{house}"]
        )
    
    # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric
    problem.addConstraint(
        lambda style1, style2, name1, name2: 
            (style1 == "victorian" and name2 == "Eric") or 
            (style2 == "victorian" and name1 == "Eric") == False,
        ["style_1", "style_2", "name_1", "name_2"]
    )
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the output structure
    header = ["House", "Name", "HouseStyle", "Smoothie", "Pet"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"style_{house}"],
            solution[f"smoothie_{house}"],
            solution[f"pet_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))