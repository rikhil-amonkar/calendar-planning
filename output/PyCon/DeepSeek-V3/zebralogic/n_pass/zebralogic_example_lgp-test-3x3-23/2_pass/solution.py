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
    def doctor_eric_adjacent(eric_house, doc_house):
        return abs(doc_house - eric_house) == 1
    
    # We need to find which house has Eric and which has doctor
    # This constraint will be applied when we know Eric's house and doctor's house
    eric_vars = [f"name_{h}" for h in houses]
    doctor_vars = [f"occupation_{h}" for h in houses]
    
    # Create a custom constraint that checks if doctor and Eric are adjacent
    def doctor_eric_constraint(*args):
        # args contains: name_1, name_2, name_3, occupation_1, occupation_2, occupation_3
        names = args[:3]
        occupations = args[3:]
        
        # Find Eric's house
        eric_house = None
        for i, name in enumerate(names):
            if name == "Eric":
                eric_house = i + 1
                break
        
        # Find doctor's house
        doctor_house = None
        for i, occ in enumerate(occupations):
            if occ == "doctor":
                doctor_house = i + 1
                break
        
        # Check if they are adjacent
        if eric_house is not None and doctor_house is not None:
            return abs(doctor_house - eric_house) == 1
        return False
    
    problem.addConstraint(doctor_eric_constraint, eric_vars + doctor_vars)
    
    # Clue 2: The person who loves cooking is directly left of the person who is a teacher
    for left_house in [1, 2]:
        right_house = left_house + 1
        problem.addConstraint(
            lambda cook_hobby, teach_occ: cook_hobby == "cooking" and teach_occ == "teacher",
            [f"hobby_{left_house}", f"occupation_{right_house}"]
        )
    
    # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening
    # This means doctor_house > garden_house
    def doctor_right_of_gardener(*args):
        # args contains: hobby_1, hobby_2, hobby_3, occupation_1, occupation_2, occupation_3
        hobbies = args[:3]
        occupations = args[3:]
        
        # Find gardener's house
        gardener_house = None
        for i, hobby in enumerate(hobbies):
            if hobby == "gardening":
                gardener_house = i + 1
                break
        
        # Find doctor's house
        doctor_house = None
        for i, occ in enumerate(occupations):
            if occ == "doctor":
                doctor_house = i + 1
                break
        
        # Check if doctor is to the right of gardener
        if gardener_house is not None and doctor_house is not None:
            return doctor_house > gardener_house
        return False
    
    hobby_vars = [f"hobby_{h}" for h in houses]
    occupation_vars = [f"occupation_{h}" for h in houses]
    problem.addConstraint(doctor_right_of_gardener, hobby_vars + occupation_vars)
    
    # Clue 4: The photography enthusiast is the person who is a teacher
    for house in houses:
        problem.addConstraint(
            lambda hobby, occ: (hobby == "photography") == (occ == "teacher"),
            [f"hobby_{house}", f"occupation_{house}"]
        )
    
    # Clue 5: The person who is an engineer is Peter
    for house in houses:
        problem.addConstraint(
            lambda name, occ: (name == "Peter") == (occ == "engineer"),
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