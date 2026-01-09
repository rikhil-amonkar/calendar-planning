import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    
    problem.addVariable("Name", names)
    problem.addVariable("HouseStyle", house_styles)
    
    def house_constraint(name, style):
        # Clue 2: Eric is in the first house
        if name == "Eric":
            return True  # Will be handled by position
        
        # Clue 1: Victorian house is to the left of colonial house
        # This will be handled by the ordering of solutions
        return True
    
    problem.addConstraint(house_constraint, ["Name", "HouseStyle"])
    
    solutions = problem.getSolutions()
    
    # Apply clue 1: Victorian is to the left of colonial
    valid_solutions = []
    for sol in solutions:
        # Since there are only 2 houses, we need to check the ordering
        # We'll generate both possible house assignments and check the clue
        for house1_name, house1_style in [(names[0], house_styles[0]), (names[0], house_styles[1]), 
                                         (names[1], house_styles[0]), (names[1], house_styles[1])]:
            house2_name = names[0] if house1_name == names[1] else names[1]
            house2_style = house_styles[0] if house1_style == house_styles[1] else house_styles[1]
            
            # Check clue 2: Eric is in first house
            if house1_name != "Eric":
                continue
                
            # Check clue 1: Victorian is to the left of colonial
            if house1_style == "victorian" and house2_style == "colonial":
                valid_solutions.append({
                    1: {"Name": house1_name, "HouseStyle": house1_style},
                    2: {"Name": house2_name, "HouseStyle": house2_style}
                })
    
    if valid_solutions:
        solution = valid_solutions[0]
        
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": []
            }
        }
        
        for house_num in sorted(solution.keys()):
            house_data = solution[house_num]
            result["solution"]["rows"].append([
                str(house_num),
                house_data["Name"],
                house_data["HouseStyle"]
            ])
        
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"})

if __name__ == "__main__":
    print(solve_puzzle())