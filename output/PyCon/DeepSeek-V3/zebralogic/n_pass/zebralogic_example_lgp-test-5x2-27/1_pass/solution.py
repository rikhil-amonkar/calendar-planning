import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    
    # Add variables for names and heights
    problem.addVariables(["name_" + str(h) for h in houses], names)
    problem.addVariables(["height_" + str(h) for h in houses], heights)
    
    # All names and heights must be different
    problem.addConstraint(lambda *args: len(set(args)) == len(args), 
                         ["name_" + str(h) for h in houses])
    problem.addConstraint(lambda *args: len(set(args)) == len(args), 
                         ["height_" + str(h) for h in houses])
    
    # Clue 1: The person who is short is in the second house.
    problem.addConstraint(lambda height_2: height_2 == "short", ["height_2"])
    
    # Clue 2: Peter is directly left of Bob.
    for i in range(1, 5):
        problem.addConstraint(
            lambda name_i, name_j: not (name_i == "Peter" and name_j != "Bob"),
            ["name_" + str(i), "name_" + str(i+1)]
        )
    # Ensure Peter is directly left of Bob exactly once
    problem.addConstraint(
        lambda n1, n2, n3, n4, n5: 
            any([n1 == "Peter" and n2 == "Bob",
                 n2 == "Peter" and n3 == "Bob",
                 n3 == "Peter" and n4 == "Bob",
                 n4 == "Peter" and n5 == "Bob"]),
        ["name_1", "name_2", "name_3", "name_4", "name_5"]
    )
    
    # Clue 3: Eric is somewhere to the left of Peter.
    problem.addConstraint(
        lambda n1, n2, n3, n4, n5: 
            (n1 == "Eric" and n2 == "Peter") or
            (n1 == "Eric" and n3 == "Peter") or
            (n1 == "Eric" and n4 == "Peter") or
            (n1 == "Eric" and n5 == "Peter") or
            (n2 == "Eric" and n3 == "Peter") or
            (n2 == "Eric" and n4 == "Peter") or
            (n2 == "Eric" and n5 == "Peter") or
            (n3 == "Eric" and n4 == "Peter") or
            (n3 == "Eric" and n5 == "Peter") or
            (n4 == "Eric" and n5 == "Peter"),
        ["name_1", "name_2", "name_3", "name_4", "name_5"]
    )
    
    # Clue 4: The person who is very tall is directly left of Peter.
    for i in range(1, 5):
        problem.addConstraint(
            lambda height_i, name_j: not (height_i == "very tall" and name_j != "Peter"),
            ["height_" + str(i), "name_" + str(i+1)]
        )
    # Ensure very tall is directly left of Peter exactly once
    problem.addConstraint(
        lambda h1, h2, h3, h4, n1, n2, n3, n4, n5: 
            any([h1 == "very tall" and n2 == "Peter",
                 h2 == "very tall" and n3 == "Peter",
                 h3 == "very tall" and n4 == "Peter",
                 h4 == "very tall" and n5 == "Peter"]),
        ["height_1", "height_2", "height_3", "height_4", 
         "name_1", "name_2", "name_3", "name_4", "name_5"]
    )
    
    # Clue 5: Alice is directly left of the person who has an average height.
    for i in range(1, 5):
        problem.addConstraint(
            lambda name_i, height_j: not (name_i == "Alice" and height_j != "average"),
            ["name_" + str(i), "height_" + str(i+1)]
        )
    # Ensure Alice is directly left of average height exactly once
    problem.addConstraint(
        lambda n1, n2, n3, n4, h1, h2, h3, h4, h5: 
            any([n1 == "Alice" and h2 == "average",
                 n2 == "Alice" and h3 == "average",
                 n3 == "Alice" and h4 == "average",
                 n4 == "Alice" and h5 == "average"]),
        ["name_1", "name_2", "name_3", "name_4",
         "height_1", "height_2", "height_3", "height_4", "height_5"]
    )
    
    # Clue 6: The person who is short and the person who is very short are next to each other.
    problem.addConstraint(
        lambda h1, h2, h3, h4, h5: 
            (h1 == "short" and h2 == "very short") or
            (h2 == "short" and h1 == "very short") or
            (h2 == "short" and h3 == "very short") or
            (h3 == "short" and h2 == "very short") or
            (h3 == "short" and h4 == "very short") or
            (h4 == "short" and h3 == "very short") or
            (h4 == "short" and h5 == "very short") or
            (h5 == "short" and h4 == "very short"),
        ["height_1", "height_2", "height_3", "height_4", "height_5"]
    )
    
    # Clue 7: The person who has an average height is in the fifth house.
    problem.addConstraint(lambda height_5: height_5 == "average", ["height_5"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Height"], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        height = solution[f"height_{house}"]
        rows.append([str(house), name, height])
    
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