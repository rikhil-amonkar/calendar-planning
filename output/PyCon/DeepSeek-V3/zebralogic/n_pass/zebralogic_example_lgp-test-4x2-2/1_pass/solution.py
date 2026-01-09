import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]
    
    problem.addVariables(["name"], names)
    problem.addVariables(["style"], styles)
    problem.addVariables(["house"], houses)
    
    # All variables must have different values
    problem.addConstraint(lambda n1, n2, n3, n4: len({n1, n2, n3, n4}) == 4, 
                         ["name_1", "name_2", "name_3", "name_4"])
    problem.addConstraint(lambda s1, s2, s3, s4: len({s1, s2, s3, s4}) == 4, 
                         ["style_1", "style_2", "style_3", "style_4"])
    
    # Clue 1: Eric is the person in a Craftsman-style house
    problem.addConstraint(lambda name, style: name == "Eric" and style == "craftsman", 
                         ["name_3", "style_3"])
    
    # Clue 2: The person in a ranch-style home is directly left of Victorian house
    problem.addConstraint(lambda s1, s2: (s1 == "ranch" and s2 == "victorian") or 
                         (s1 != "ranch" and s2 != "victorian") or
                         (s1 != "ranch" and s2 == "victorian") or
                         (s1 == "ranch" and s2 != "victorian"), 
                         ["style_1", "style_2"])
    problem.addConstraint(lambda s2, s3: (s2 == "ranch" and s3 == "victorian") or 
                         (s2 != "ranch" and s3 != "victorian") or
                         (s2 != "ranch" and s3 == "victorian") or
                         (s2 == "ranch" and s3 != "victorian"), 
                         ["style_2", "style_3"])
    problem.addConstraint(lambda s3, s4: (s3 == "ranch" and s4 == "victorian") or 
                         (s3 != "ranch" and s4 != "victorian") or
                         (s3 != "ranch" and s4 == "victorian") or
                         (s3 == "ranch" and s4 != "victorian"), 
                         ["style_3", "style_4"])
    
    # Add direct constraint for clue 2
    def ranch_left_of_victorian(s1, s2, s3, s4):
        ranch_pos = None
        victorian_pos = None
        for i, style in enumerate([s1, s2, s3, s4], 1):
            if style == "ranch":
                ranch_pos = i
            if style == "victorian":
                victorian_pos = i
        return ranch_pos is not None and victorian_pos is not None and ranch_pos + 1 == victorian_pos
    
    problem.addConstraint(ranch_left_of_victorian, ["style_1", "style_2", "style_3", "style_4"])
    
    # Clue 3: Eric is in the third house
    problem.addConstraint(lambda name: name == "Eric", ["name_3"])
    
    # Clue 4: Arnold is in the fourth house
    problem.addConstraint(lambda name: name == "Arnold", ["name_4"])
    
    # Clue 5: The person residing in a Victorian house is Alice
    problem.addConstraint(lambda name, style: not (style == "victorian") or name == "Alice", 
                         ["name_1", "style_1"])
    problem.addConstraint(lambda name, style: not (style == "victorian") or name == "Alice", 
                         ["name_2", "style_2"])
    problem.addConstraint(lambda name, style: not (style == "victorian") or name == "Alice", 
                         ["name_3", "style_3"])
    problem.addConstraint(lambda name, style: not (style == "victorian") or name == "Alice", 
                         ["name_4", "style_4"])
    
    # Create variables for each house
    name_vars = ["name_1", "name_2", "name_3", "name_4"]
    style_vars = ["style_1", "style_2", "style_3", "style_4"]
    
    for var in name_vars + style_vars:
        problem.addVariables([var], names if var.startswith("name") else styles)
    
    # Each house has exactly one name and one style
    for i in range(1, 5):
        problem.addConstraint(lambda n, s: True, [f"name_{i}", f"style_{i}"])
    
    # All names are different
    problem.addConstraint(lambda n1, n2, n3, n4: len({n1, n2, n3, n4}) == 4, name_vars)
    
    # All styles are different
    problem.addConstraint(lambda s1, s2, s3, s4: len({s1, s2, s3, s4}) == 4, style_vars)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "HouseStyle"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for i in range(1, 5):
        house_num = str(i)
        name = solution[f"name_{i}"]
        style = solution[f"style_{i}"]
        rows.append([house_num, name, style])
    
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))