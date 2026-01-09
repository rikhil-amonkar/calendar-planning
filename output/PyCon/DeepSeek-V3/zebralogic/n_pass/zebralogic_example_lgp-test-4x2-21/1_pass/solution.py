import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]
    
    # Add variables - house positions for names and styles
    problem.addVariables(["name_" + str(h) for h in houses], names)
    problem.addVariables(["style_" + str(h) for h in houses], styles)
    
    # All names and styles must be different
    problem.addConstraint(lambda n1, n2, n3, n4: len({n1, n2, n3, n4}) == 4, 
                         ["name_1", "name_2", "name_3", "name_4"])
    problem.addConstraint(lambda s1, s2, s3, s4: len({s1, s2, s3, s4}) == 4, 
                         ["style_1", "style_2", "style_3", "style_4"])
    
    # Clue 1: Alice is in the second house
    problem.addConstraint(lambda n2: n2 == "Alice", ["name_2"])
    
    # Clue 2: The person residing in a Victorian house is directly left of Peter
    for i in range(1, 4):  # Victorian can only be in houses 1-3 (since Peter must be to the right)
        def victorian_left_of_peter(style_i, name_i, name_next):
            return (style_i == "victorian" and name_next == "Peter")
        problem.addConstraint(victorian_left_of_peter, 
                            [f"style_{i}", f"name_{i}", f"name_{i+1}"])
    
    # Clue 3: Peter is somewhere to the right of the person in a ranch-style home
    for i in range(1, 4):  # Ranch can be in houses 1-3
        for j in range(i+1, 5):  # Peter must be in a house to the right
            def peter_right_of_ranch(style_i, name_j):
                return not (style_i == "ranch" and name_j == "Peter")
            problem.addConstraint(peter_right_of_ranch, [f"style_{i}", f"name_{j}"])
    
    # Add positive constraint for clue 3: There exists a ranch house with Peter to its right
    def ranch_with_peter_right(style1, style2, style3, style4, name1, name2, name3, name4):
        ranch_positions = [i for i, style in enumerate([style1, style2, style3, style4], 1) if style == "ranch"]
        peter_positions = [i for i, name in enumerate([name1, name2, name3, name4], 1) if name == "Peter"]
        if not ranch_positions or not peter_positions:
            return False
        ranch_pos = ranch_positions[0]
        peter_pos = peter_positions[0]
        return peter_pos > ranch_pos
    problem.addConstraint(ranch_with_peter_right, 
                        ["style_1", "style_2", "style_3", "style_4", 
                         "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house
    for i in range(1, 4):  # Craftsman can be in houses 1-3
        for j in range(i+1, 5):  # Arnold must be in a house to the right
            def arnold_right_of_craftsman(style_i, name_j):
                return not (style_i == "craftsman" and name_j == "Arnold")
            problem.addConstraint(arnold_right_of_craftsman, [f"style_{i}", f"name_{j}"])
    
    # Add positive constraint for clue 4: There exists a craftsman house with Arnold to its right
    def craftsman_with_arnold_right(style1, style2, style3, style4, name1, name2, name3, name4):
        craftsman_positions = [i for i, style in enumerate([style1, style2, style3, style4], 1) if style == "craftsman"]
        arnold_positions = [i for i, name in enumerate([name1, name2, name3, name4], 1) if name == "Arnold"]
        if not craftsman_positions or not arnold_positions:
            return False
        craftsman_pos = craftsman_positions[0]
        arnold_pos = arnold_positions[0]
        return arnold_pos > craftsman_pos
    problem.addConstraint(craftsman_with_arnold_right, 
                        ["style_1", "style_2", "style_3", "style_4", 
                         "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 5: The person in a Craftsman-style house is Alice
    problem.addConstraint(lambda s2, n2: not (s2 == "craftsman" and n2 != "Alice"), ["style_2", "name_2"])
    problem.addConstraint(lambda s1, n1: not (s1 == "craftsman" and n1 != "Alice"), ["style_1", "name_1"])
    problem.addConstraint(lambda s3, n3: not (s3 == "craftsman" and n3 != "Alice"), ["style_3", "name_3"])
    problem.addConstraint(lambda s4, n4: not (s4 == "craftsman" and n4 != "Alice"), ["style_4", "name_4"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "HouseStyle"], "rows": []}}
    
    # Use the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        style = solution[f"style_{house}"]
        rows.append([str(house), name, style])
    
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