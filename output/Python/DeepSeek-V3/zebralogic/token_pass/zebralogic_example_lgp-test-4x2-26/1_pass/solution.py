import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]
    houses = [1, 2, 3, 4]
    
    # Generate all permutations of names and occupations
    name_perms = permutations(names, 4)
    occ_perms = permutations(occupations, 4)
    
    solutions = []
    
    # Try all combinations
    for name_assign in name_perms:
        for occ_assign in occ_perms:
            # Create assignment dictionaries
            assignment = {}
            for i in range(4):
                house = i + 1
                assignment[house] = {
                    'name': name_assign[i],
                    'occupation': occ_assign[i]
                }
            
            # Check clue 1: Two houses between Eric and Peter
            eric_house = None
            peter_house = None
            for house in houses:
                if assignment[house]['name'] == 'Eric':
                    eric_house = house
                if assignment[house]['name'] == 'Peter':
                    peter_house = house
            
            if eric_house is None or peter_house is None:
                continue
            if abs(eric_house - peter_house) != 3:  # 3 houses apart means 2 between
                continue
            
            # Check clue 2: Teacher is Peter
            teacher_house = None
            for house in houses:
                if assignment[house]['occupation'] == 'teacher':
                    teacher_house = house
                    break
            
            if teacher_house is None:
                continue
            if assignment[teacher_house]['name'] != 'Peter':
                continue
            
            # Check clue 3: Peter is not in first house
            if peter_house == 1:
                continue
            
            # Check clue 4: One house between doctor and Alice
            doctor_house = None
            alice_house = None
            for house in houses:
                if assignment[house]['occupation'] == 'doctor':
                    doctor_house = house
                if assignment[house]['name'] == 'Alice':
                    alice_house = house
            
            if doctor_house is None or alice_house is None:
                continue
            if abs(doctor_house - alice_house) != 2:  # 2 houses apart means 1 between
                continue
            
            # Check clue 5: Artist is Alice
            artist_house = None
            for house in houses:
                if assignment[house]['occupation'] == 'artist':
                    artist_house = house
                    break
            
            if artist_house is None:
                continue
            if assignment[artist_house]['name'] != 'Alice':
                continue
            
            # All clues satisfied
            solutions.append(assignment)
    
    if not solutions:
        return {"error": "No solution found"}
    
    # Take the first valid solution
    solution = solutions[0]
    
    # Format output
    rows = []
    for house in houses:
        rows.append([
            str(house),
            solution[house]['name'],
            solution[house]['occupation']
        ])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))