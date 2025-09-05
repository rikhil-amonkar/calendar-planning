import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']
    houses = [1, 2, 3]
    
    # Generate all possible permutations
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for hobby_perm in permutations(hobbies):
                # Create assignment for each house
                assignment = []
                for i in range(3):
                    assignment.append({
                        'house': houses[i],
                        'name': name_perm[i],
                        'occupation': occ_perm[i],
                        'hobby': hobby_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Clue 1: The person who is a doctor and Eric are next to each other
                doctor_house = None
                eric_house = None
                for house in assignment:
                    if house['occupation'] == 'doctor':
                        doctor_house = house['house']
                    if house['name'] == 'Eric':
                        eric_house = house['house']
                
                if doctor_house is None or eric_house is None or abs(doctor_house - eric_house) != 1:
                    valid = False
                    continue
                
                # Clue 2: The person who loves cooking is directly left of the person who is a teacher
                cooking_house = None
                teacher_house = None
                for house in assignment:
                    if house['hobby'] == 'cooking':
                        cooking_house = house['house']
                    if house['occupation'] == 'teacher':
                        teacher_house = house['house']
                
                if cooking_house is None or teacher_house is None or cooking_house + 1 != teacher_house:
                    valid = False
                    continue
                
                # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening
                gardening_house = None
                for house in assignment:
                    if house['hobby'] == 'gardening':
                        gardening_house = house['house']
                
                if gardening_house is None or doctor_house <= gardening_house:
                    valid = False
                    continue
                
                # Clue 4: The photography enthusiast is the person who is a teacher
                for house in assignment:
                    if house['hobby'] == 'photography' and house['occupation'] != 'teacher':
                        valid = False
                        break
                    if house['occupation'] == 'teacher' and house['hobby'] != 'photography':
                        valid = False
                        break
                
                if not valid:
                    continue
                
                # Clue 5: The person who is an engineer is Peter
                for house in assignment:
                    if house['occupation'] == 'engineer' and house['name'] != 'Peter':
                        valid = False
                        break
                    if house['name'] == 'Peter' and house['occupation'] != 'engineer':
                        valid = False
                        break
                
                if valid:
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "Hobby"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment, key=lambda x: x['house']):
                        solution["solution"]["rows"].append([
                            str(house['house']),
                            house['name'],
                            house['occupation'],
                            house['hobby']
                        ])
                    
                    return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()