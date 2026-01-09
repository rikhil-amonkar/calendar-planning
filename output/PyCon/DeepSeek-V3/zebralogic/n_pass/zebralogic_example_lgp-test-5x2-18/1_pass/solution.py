import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: houses 1-5
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for names and children
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]
    
    # Add variables for name and child for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"child_{house}", children)
    
    # All names and children must be different
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"child_{house}" for house in houses])
    
    # Clue 1: Bob is somewhere to the left of the person whose child is named Samantha
    def left_of(solver, house1, child1, house2, child2):
        if child1 == "Samantha" and child2 == "Samantha":
            return False
        if child2 == "Samantha":
            return house1 < house2
        return True
    
    for h1 in houses:
        for h2 in houses:
            if h1 != h2:
                problem.addConstraint(
                    lambda name_h1, child_h1, name_h2, child_h2: 
                    not (name_h1 == "Bob" and child_h2 == "Samantha") or h1 < h2,
                    [f"name_{h1}", f"child_{h1}", f"name_{h2}", f"child_{h2}"]
                )
    
    # Clue 2: The person who is the mother of Timothy is somewhere to the left of the person whose child is named Samantha
    for h1 in houses:
        for h2 in houses:
            if h1 != h2:
                problem.addConstraint(
                    lambda child_h1, child_h2: 
                    not (child_h1 == "Timothy" and child_h2 == "Samantha") or h1 < h2,
                    [f"child_{h1}", f"child_{h2}"]
                )
    
    # Clue 3: The person whose child is named Fred is in the second house
    problem.addConstraint(lambda child: child == "Fred", ["child_2"])
    
    # Clue 4: There is one house between Alice and the person whose child is named Samantha
    def one_house_between(solver, name_val, child_val, house1, house2):
        if name_val == "Alice" and child_val == "Samantha":
            return abs(house1 - house2) == 2
        return True
    
    for h1 in houses:
        for h2 in houses:
            if h1 != h2:
                problem.addConstraint(
                    lambda name_h1, child_h2, h1=h1, h2=h2: 
                    not (name_h1 == "Alice" and child_h2 == "Samantha") or abs(h1 - h2) == 2,
                    [f"name_{h1}", f"child_{h2}"]
                )
    
    # Clue 5: Eric is not in the third house
    problem.addConstraint(lambda name: name != "Eric", ["name_3"])
    
    # Clue 6: Bob is not in the third house
    problem.addConstraint(lambda name: name != "Bob", ["name_3"])
    
    # Clue 7: The person whose child is named Fred is directly left of the person whose child is named Bella
    problem.addConstraint(lambda child2, child3: child2 == "Fred" and child3 == "Bella", ["child_2", "child_3"])
    
    # Clue 8: The person whose child is named Samantha is somewhere to the left of Peter
    for h1 in houses:
        for h2 in houses:
            if h1 != h2:
                problem.addConstraint(
                    lambda child_h1, name_h2: 
                    not (child_h1 == "Samantha" and name_h2 == "Peter") or h1 < h2,
                    [f"child_{h1}", f"name_{h2}"]
                )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Children"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        child = solution[f"child_{house}"]
        rows.append([str(house), name, child])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))