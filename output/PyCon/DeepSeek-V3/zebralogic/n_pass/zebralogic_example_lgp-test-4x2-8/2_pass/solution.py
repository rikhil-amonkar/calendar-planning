import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    
    # Define variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", ["Peter", "Arnold", "Alice", "Eric"])
        problem.addVariable(f"color_{house}", ["yellow", "green", "red", "white"])
    
    # All names and colors must be different
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"color_{house}" for house in houses])
    
    # Clue 1: Green is in house 3
    problem.addConstraint(lambda color_3: color_3 == "green", ["color_3"])
    
    # Clue 2: Peter is in house 1
    problem.addConstraint(lambda name_1: name_1 == "Peter", ["name_1"])
    
    # Clue 3: One house between red and yellow
    def one_house_between(color_1, color_2, color_3, color_4):
        colors = [color_1, color_2, color_3, color_4]
        red_idx = colors.index("red") + 1
        yellow_idx = colors.index("yellow") + 1
        return abs(red_idx - yellow_idx) == 2
    problem.addConstraint(one_house_between, ["color_1", "color_2", "color_3", "color_4"])
    
    # Clue 4: Arnold is directly left of Eric
    def arnold_left_eric(name_1, name_2, name_3, name_4):
        names = [name_1, name_2, name_3, name_4]
        try:
            arnold_idx = names.index("Arnold")
            eric_idx = names.index("Eric")
            return eric_idx - arnold_idx == 1
        except ValueError:
            return False
    problem.addConstraint(arnold_left_eric, ["name_1", "name_2", "name_3", "name_4"])
    
    # Clue 5: Eric loves yellow
    def eric_yellow(name_1, name_2, name_3, name_4, color_1, color_2, color_3, color_4):
        names = [name_1, name_2, name_3, name_4]
        colors = [color_1, color_2, color_3, color_4]
        try:
            eric_idx = names.index("Eric")
            return colors[eric_idx] == "yellow"
        except ValueError:
            return False
    problem.addConstraint(eric_yellow, ["name_1", "name_2", "name_3", "name_4", "color_1", "color_2", "color_3", "color_4"])
    
    # Get solution
    solutions = problem.getSolutions()
    if not solutions:
        return None
    
    solution = solutions[0]
    
    # Build result
    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": []
        }
    }
    
    for house in houses:
        house_num = str(house)
        name = solution[f"name_{house}"]
        color = solution[f"color_{house}"]
        result["solution"]["rows"].append([house_num, name, color])
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))