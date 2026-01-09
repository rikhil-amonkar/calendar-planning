import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3]
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]
    
    # Add variables for each house
    problem.addVariables(["name1", "name2", "name3"], names)
    problem.addVariables(["height1", "height2", "height3"], heights)
    
    # All names and heights must be different
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, ["name1", "name2", "name3"])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, ["height1", "height2", "height3"])
    
    # Clue 1: Peter is somewhere to the right of Eric
    def peter_right_of_eric(n1, n2, n3):
        eric_pos = None
        peter_pos = None
        for i, name in enumerate([n1, n2, n3], 1):
            if name == "Eric":
                eric_pos = i
            if name == "Peter":
                peter_pos = i
        return peter_pos is not None and eric_pos is not None and peter_pos > eric_pos
    
    problem.addConstraint(peter_right_of_eric, ["name1", "name2", "name3"])
    
    # Clue 2: The person who is short is in the first house
    problem.addConstraint(lambda h: h == "short", ["height1"])
    
    # Clue 3: There is one house between the person who is short and the person who is very short
    def one_between_short_and_very_short(h1, h2, h3):
        short_pos = 1  # From clue 2
        very_short_pos = None
        for i, height in enumerate([h1, h2, h3], 1):
            if height == "very short":
                very_short_pos = i
        return very_short_pos is not None and abs(short_pos - very_short_pos) == 2
    
    problem.addConstraint(one_between_short_and_very_short, ["height1", "height2", "height3"])
    
    # Clue 4: Arnold and the person who is very short are next to each other
    def arnold_next_to_very_short(n1, n2, n3, h1, h2, h3):
        arnold_pos = None
        very_short_pos = None
        for i, (name, height) in enumerate(zip([n1, n2, n3], [h1, h2, h3]), 1):
            if name == "Arnold":
                arnold_pos = i
            if height == "very short":
                very_short_pos = i
        return arnold_pos is not None and very_short_pos is not None and abs(arnold_pos - very_short_pos) == 1
    
    problem.addConstraint(arnold_next_to_very_short, ["name1", "name2", "name3", "height1", "height2", "height3"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Height"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for i in range(1, 4):
        name_key = f"name{i}"
        height_key = f"height{i}"
        rows.append([str(i), solution[name_key], solution[height_key]])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))