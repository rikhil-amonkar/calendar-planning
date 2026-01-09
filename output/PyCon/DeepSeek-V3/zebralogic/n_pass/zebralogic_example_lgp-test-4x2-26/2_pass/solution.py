import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]
    
    # Add variables for each house position
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"occupation_{house}", occupations)
    
    # All names and occupations must be different
    problem.addConstraint(lambda n1, n2, n3, n4: len({n1, n2, n3, n4}) == 4, 
                         ["name_1", "name_2", "name_3", "name_4"])
    problem.addConstraint(lambda o1, o2, o3, o4: len({o1, o2, o3, o4}) == 4, 
                         ["occupation_1", "occupation_2", "occupation_3", "occupation_4"])
    
    # Clue 1: There are two houses between Eric and Peter
    # This means they are at positions 1 and 4, or 4 and 1
    def eric_peter_positions():
        eric_peter_constraints = []
        for i in houses:
            for j in houses:
                if abs(i - j) == 3:  # Two houses between means distance of 3
                    eric_peter_constraints.append((i, j))
        return eric_peter_constraints
    
    # Add Eric and Peter position constraints
    eric_peter_pairs = eric_peter_positions()
    for eric_house, peter_house in eric_peter_pairs:
        # We'll create a custom constraint that checks if Eric is in one house and Peter in the other
        def eric_peter_constraint(*args):
            names = args[:4]  # First 4 args are names for houses 1-4
            eric_in_correct_house = names[eric_house-1] == "Eric"
            peter_in_correct_house = names[peter_house-1] == "Peter"
            return eric_in_correct_house and peter_in_correct_house
        
        problem.addConstraint(eric_peter_constraint, 
                            ["name_1", "name_2", "name_3", "name_4"])
    
    # Clue 2: The person who is a teacher is Peter
    for house in houses:
        problem.addConstraint(lambda name, occ, h=house: not (occ == "teacher") or (name == "Peter"), 
                             [f"name_{house}", f"occupation_{house}"])
    
    # Clue 3: Peter is not in the first house
    problem.addConstraint(lambda name: name != "Peter", ["name_1"])
    
    # Clue 4: There is one house between the person who is a doctor and Alice
    # This means they are at positions like (1,3), (2,4), (3,1), (4,2)
    def doctor_alice_positions():
        doctor_alice_constraints = []
        for i in houses:
            for j in houses:
                if abs(i - j) == 2:  # One house between means distance of 2
                    doctor_alice_constraints.append((i, j))
        return doctor_alice_constraints
    
    # Add doctor and Alice position constraints
    doctor_alice_pairs = doctor_alice_positions()
    for doctor_house, alice_house in doctor_alice_pairs:
        def doctor_alice_constraint(*args):
            names = args[:4]  # First 4 args are names for houses 1-4
            occupations = args[4:8]  # Next 4 args are occupations for houses 1-4
            alice_in_correct_house = names[alice_house-1] == "Alice"
            doctor_in_correct_house = occupations[doctor_house-1] == "doctor"
            return alice_in_correct_house and doctor_in_correct_house
        
        problem.addConstraint(doctor_alice_constraint, 
                            ["name_1", "name_2", "name_3", "name_4",
                             "occupation_1", "occupation_2", "occupation_3", "occupation_4"])
    
    # Clue 5: The person who is an artist is Alice
    for house in houses:
        problem.addConstraint(lambda name, occ, h=house: not (occ == "artist") or (name == "Alice"), 
                             [f"name_{house}", f"occupation_{house}"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Occupation"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    rows = []
    for house in sorted(houses):
        name = solution[f"name_{house}"]
        occupation = solution[f"occupation_{house}"]
        rows.append([str(house), name, occupation])
    
    return {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))