import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]
    
    # Add variables for names and occupations
    problem.addVariables(["name"], names)
    problem.addVariables(["occupation"], occupations)
    
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
    def two_houses_between(eric_pos, peter_pos):
        return abs(eric_pos - peter_pos) == 3
    
    # Find positions for Eric and Peter
    eric_positions = []
    peter_positions = []
    for house in houses:
        problem.addConstraint(lambda name, h=house: name != "Eric" or eric_positions.append(h), [f"name_{house}"])
        problem.addConstraint(lambda name, h=house: name != "Peter" or peter_positions.append(h), [f"name_{house}"])
    
    # Apply constraint after positions are determined
    problem.addConstraint(two_houses_between, ["eric_pos", "peter_pos"])
    
    # Clue 2: The person who is a teacher is Peter
    for house in houses:
        problem.addConstraint(lambda name, occ, h=house: not (occ == "teacher") or (name == "Peter"), 
                             [f"name_{house}", f"occupation_{house}"])
    
    # Clue 3: Peter is not in the first house
    problem.addConstraint(lambda name: name != "Peter", ["name_1"])
    
    # Clue 4: There is one house between the person who is a doctor and Alice
    def one_house_between(doctor_pos, alice_pos):
        return abs(doctor_pos - alice_pos) == 2
    
    # Find positions for doctor and Alice
    doctor_positions = []
    alice_positions = []
    for house in houses:
        problem.addConstraint(lambda occ, h=house: occ != "doctor" or doctor_positions.append(h), [f"occupation_{house}"])
        problem.addConstraint(lambda name, h=house: name != "Alice" or alice_positions.append(h), [f"name_{house}"])
    
    # Apply constraint after positions are determined
    problem.addConstraint(one_house_between, ["doctor_pos", "alice_pos"])
    
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