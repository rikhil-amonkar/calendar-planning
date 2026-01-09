import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables for each attribute
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"hobby_{house}", hobbies)
        problem.addVariable(f"pet_{house}", pets)
        problem.addVariable(f"height_{house}", heights)
    
    # All attributes must be different within their category
    problem.addConstraint(lambda n1, n2: n1 != n2, [f"name_{house}" for house in houses])
    problem.addConstraint(lambda h1, h2: h1 != h2, [f"hobby_{house}" for house in houses])
    problem.addConstraint(lambda p1, p2: p1 != p2, [f"pet_{house}" for house in houses])
    problem.addConstraint(lambda h1, h2: h1 != h2, [f"height_{house}" for house in houses])
    
    # Clue 1: The person who is very short is the photography enthusiast.
    for house in houses:
        problem.addConstraint(
            lambda height, hobby, h=house: not (height == "very short" and hobby != "photography"),
            [f"height_{house}", f"hobby_{house}"]
        )
        problem.addConstraint(
            lambda height, hobby, h=house: not (hobby == "photography" and height != "very short"),
            [f"height_{house}", f"hobby_{house}"]
        )
    
    # Clue 2: Eric is the person who is very short.
    for house in houses:
        problem.addConstraint(
            lambda name, height, h=house: not (name == "Eric" and height != "very short"),
            [f"name_{house}", f"height_{house}"]
        )
        problem.addConstraint(
            lambda name, height, h=house: not (height == "very short" and name != "Eric"),
            [f"name_{house}", f"height_{house}"]
        )
    
    # Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
    problem.addConstraint(
        lambda height1, pet1, height2, pet2: not (
            (height1 == "very short" and pet1 == "cat") or
            (height2 == "very short" and pet2 == "cat")
        ) or (height1 == "very short" and pet2 == "cat"),
        ["height_1", "pet_1", "height_2", "pet_2"]
    )
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Use the first solution
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Hobby", "Pet", "Height"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"hobby_{house}"],
            solution[f"pet_{house}"],
            solution[f"height_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))