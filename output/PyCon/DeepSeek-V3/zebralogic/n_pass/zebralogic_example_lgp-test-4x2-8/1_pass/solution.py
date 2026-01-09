import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]
    
    problem.addVariables(["name"], [names])
    problem.addVariables(["color"], [colors])
    
    # Clue 1: Green is in house 3
    problem.addConstraint(lambda color, house: color[house-1] == "green", ("color", "house"))
    
    # Clue 2: Peter is in house 1
    problem.addConstraint(lambda name, house: name[house-1] == "Peter", ("name", "house"))
    
    # Clue 3: One house between red and yellow
    def one_house_between(color):
        red_idx = color.index("red") + 1
        yellow_idx = color.index("yellow") + 1
        return abs(red_idx - yellow_idx) == 2
    problem.addConstraint(one_house_between, ("color",))
    
    # Clue 4: Arnold is directly left of Eric
    def arnold_left_eric(name):
        arnold_idx = name.index("Arnold") + 1
        eric_idx = name.index("Eric") + 1
        return eric_idx - arnold_idx == 1
    problem.addConstraint(arnold_left_eric, ("name",))
    
    # Clue 5: Eric loves yellow
    def eric_yellow(name, color):
        eric_idx = name.index("Eric")
        return color[eric_idx] == "yellow"
    problem.addConstraint(eric_yellow, ("name", "color"))
    
    # All names and colors are unique per house
    problem.addConstraint(AllDifferentConstraint(), ("name",))
    problem.addConstraint(AllDifferentConstraint(), ("color",))
    
    # Get solution
    solutions = problem.getSolutions()
    if not solutions:
        return None
    
    solution = solutions[0]
    name_assignment = solution["name"]
    color_assignment = solution["color"]
    
    # Build result
    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": []
        }
    }
    
    for i in range(4):
        house_num = str(i + 1)
        name = name_assignment[i]
        color = color_assignment[i]
        result["solution"]["rows"].append([house_num, name, color])
    
    return result

if __name__ == "__main__":
    from constraint import AllDifferentConstraint
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))