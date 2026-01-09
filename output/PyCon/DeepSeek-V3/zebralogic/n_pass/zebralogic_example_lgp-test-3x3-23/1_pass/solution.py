import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables: house numbers 1, 2, 3
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"occupation_{house}", occupations)
        problem.addVariable(f"hobby_{house}", hobbies)
    
    # All attributes must be different across houses
    problem.addConstraint(lambda n1, n2, n3: len({n1, n2, n3}) == 3, 
                         [f"name_{h}" for h in houses])
    problem.addConstraint(lambda o1, o2, o3: len({o1, o2, o3}) == 3, 
                         [f"occupation_{h}" for h in houses])
    problem.addConstraint(lambda h1, h2, h3: len({h1, h2, h3}) == 3, 
                         [f"hobby_{h}" for h in houses])
    
    # Clue 1: The person who is a doctor and Eric are next to each other
    def doctor_eric_adjacent(doc_house, eric_house):
        return abs(doc_house - eric_house) == 1
    
    # Find which house has doctor and which has Eric
    for h1 in houses:
        for h2 in houses:
            if h1 != h2:
                problem.addConstraint(
                    doctor_eric_adjacent,
                    [f"occupation_{h1}", f"name_{h2}"],
                    {f"occupation_{h1}": "doctor", f"name_{h2}": "Eric"}
                )
    
    # Clue 2: The person who loves cooking is directly left of the person who is a teacher
    for left_house in [1, 2]:
        right_house = left_house + 1
        problem.addConstraint(
            lambda cook_hobby, teach_occ: cook_hobby == "cooking" and teach_occ == "teacher",
            [f"hobby_{left_house}", f"occupation_{right_house}"]
        )
    
    # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening
    for garden_house in houses:
        for doctor_house in houses:
            if garden_house >= doctor_house:
                problem.addConstraint(
                    lambda g_hobby, d_occ: not (g_hobby == "gardening" and d_occ == "doctor"),
                    [f"hobby_{garden_house}", f"occupation_{doctor_house}"]
                )
    
    # Clue 4: The photography enthusiast is the person who is a teacher
    for house in houses:
        problem.addConstraint(
            lambda hobby, occ: not (hobby == "photography" and occ != "teacher"),
            [f"hobby_{house}", f"occupation_{house}"]
        )
        problem.addConstraint(
            lambda hobby, occ: not (hobby != "photography" and occ == "teacher"),
            [f"hobby_{house}", f"occupation_{house}"]
        )
    
    # Clue 5: The person who is an engineer is Peter
    for house in houses:
        problem.addConstraint(
            lambda name, occ: not (name == "Peter" and occ != "engineer"),
            [f"name_{house}", f"occupation_{house}"]
        )
        problem.addConstraint(
            lambda name, occ: not (name != "Peter" and occ == "engineer"),
            [f"name_{house}", f"occupation_{house}"]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Occupation", "Hobby"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in sorted(houses):
        name = solution[f"name_{house}"]
        occupation = solution[f"occupation_{house}"]
        hobby = solution[f"hobby_{house}"]
        rows.append([str(house), name, occupation, hobby])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))