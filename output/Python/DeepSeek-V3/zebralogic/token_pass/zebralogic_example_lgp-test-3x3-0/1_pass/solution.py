import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each attribute
    name_perms = permutations(names, 3)
    edu_perms = permutations(educations, 3)
    occ_perms = permutations(occupations, 3)
    
    solutions = []
    
    # Try all combinations
    for name_assignment in name_perms:
        for edu_assignment in edu_perms:
            for occ_assignment in occ_perms:
                # Create mapping for each house
                assignment = {}
                valid = True
                
                for i in range(3):
                    house = houses[i]
                    assignment[house] = {
                        'name': name_assignment[i],
                        'education': edu_assignment[i],
                        'occupation': occ_assignment[i]
                    }
                
                # Clue 1: The person who is a teacher is directly left of the person with an associate's degree
                teacher_house = None
                associate_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'teacher':
                        teacher_house = house
                    if assignment[house]['education'] == 'associate':
                        associate_house = house
                
                if not (teacher_house is not None and associate_house is not None and 
                        associate_house == teacher_house + 1):
                    valid = False
                
                # Clue 2: The person with an associate's degree and Eric are next to each other
                if valid:
                    eric_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Eric':
                            eric_house = house
                            break
                    
                    if not (abs(associate_house - eric_house) == 1):
                        valid = False
                
                # Clue 3: Peter is the person with a high school diploma
                if valid:
                    for house in houses:
                        if assignment[house]['name'] == 'Peter' and assignment[house]['education'] != 'high school':
                            valid = False
                            break
                        if assignment[house]['education'] == 'high school' and assignment[house]['name'] != 'Peter':
                            valid = False
                            break
                
                # Clue 4: The person who is a doctor is the person with a bachelor's degree
                if valid:
                    for house in houses:
                        if assignment[house]['occupation'] == 'doctor' and assignment[house]['education'] != 'bachelor':
                            valid = False
                            break
                        if assignment[house]['education'] == 'bachelor' and assignment[house]['occupation'] != 'doctor':
                            valid = False
                            break
                
                if valid:
                    solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        solution = solutions[0]  # Should be unique
        rows = []
        for house in sorted(solution.keys()):
            data = solution[house]
            rows.append([
                str(house),
                data['name'],
                data['education'],
                data['occupation']
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": rows
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())