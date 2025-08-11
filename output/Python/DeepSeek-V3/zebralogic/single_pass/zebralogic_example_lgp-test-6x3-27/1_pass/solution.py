import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    cars = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']
    
    # Generate all possible permutations for each category (will be filtered by constraints)
    # We'll represent each house as a dictionary with attributes
    
    # We'll iterate through all possible assignments that satisfy the constraints
    # Since brute force is impractical, we'll use constraint satisfaction
    
    # Let's create a list of houses
    houses = [{'House': str(i+1)} for i in range(6)]
    
    # We'll use backtracking to assign attributes
    
    from copy import deepcopy
    
    def backtrack(assignment, remaining_names, remaining_occupations, remaining_cars, index):
        if index == 6:
            # Check all constraints
            if check_all_constraints(assignment):
                return assignment
            else:
                return None
                
        for name in list(remaining_names):
            new_assignment = deepcopy(assignment)
            new_remaining_names = deepcopy(remaining_names)
            new_remaining_names.remove(name)
            new_assignment[index]['Name'] = name
            
            for occupation in list(remaining_occupations):
                new_assignment2 = deepcopy(new_assignment)
                new_remaining_occupations = deepcopy(remaining_occupations)
                new_remaining_occupations.remove(occupation)
                new_assignment2[index]['Occupation'] = occupation
                
                for car in list(remaining_cars):
                    new_assignment3 = deepcopy(new_assignment2)
                    new_remaining_cars = deepcopy(remaining_cars)
                    new_remaining_cars.remove(car)
                    new_assignment3[index]['Car'] = car
                    
                    # Check constraints that can be checked at this level
                    if check_partial_constraints(new_assignment3, index):
                        result = backtrack(new_assignment3, new_remaining_names, new_remaining_occupations, new_remaining_cars, index + 1)
                        if result is not None:
                            return result
        return None
    
    def check_partial_constraints(assignment, index):
        # Check constraints that can be verified with the current partial assignment
        for i in range(index + 1):
            house = assignment[i]
            
            # Clue 1: Ford F-150 is in house 5
            if i == 4 and 'Car' in house and house['Car'] != 'ford f150':
                return False
            if i != 4 and 'Car' in house and house['Car'] == 'ford f150':
                return False
                
            # Clue 2: Chevrolet not in house 2
            if i == 1 and 'Car' in house and house['Car'] == 'chevrolet silverado':
                return False
                
            # Clue 4: Lawyer not in house 5
            if i == 4 and 'Occupation' in house and house['Occupation'] == 'lawyer':
                return False
                
            # Clue 6: Carol is right of Eric
            if 'Name' in house:
                if house['Name'] == 'Carol':
                    # Check if Eric is to the left
                    eric_found = False
                    for j in range(i):
                        if assignment[j]['Name'] == 'Eric':
                            eric_found = True
                            break
                    if not eric_found:
                        return False
                if house['Name'] == 'Eric':
                    # Check no Carol to the left
                    for j in range(i):
                        if assignment[j]['Name'] == 'Carol':
                            return False
                            
            # Clue 7: Doctor is Eric
            if 'Name' in house and 'Occupation' in house:
                if house['Name'] == 'Eric' and house['Occupation'] != 'doctor':
                    return False
                if house['Occupation'] == 'doctor' and house['Name'] != 'Eric':
                    return False
                    
            # Clue 9: Carol not in house 6
            if i == 5 and 'Name' in house and house['Name'] == 'Carol':
                return False
                
            # Clue 10: Engineer is Bob
            if 'Name' in house and 'Occupation' in house:
                if house['Name'] == 'Bob' and house['Occupation'] != 'engineer':
                    return False
                if house['Occupation'] == 'engineer' and house['Name'] != 'Bob':
                    return False
                    
            # Clue 14: Artist is Arnold
            if 'Name' in house and 'Occupation' in house:
                if house['Name'] == 'Arnold' and house['Occupation'] != 'artist':
                    return False
                if house['Occupation'] == 'artist' and house['Name'] != 'Arnold':
                    return False
                    
        return True
    
    def check_all_constraints(assignment):
        # Check all constraints on complete assignment
        
        # Clue 1: Ford F-150 is in house 5
        if assignment[4]['Car'] != 'ford f150':
            return False
            
        # Clue 2: Chevrolet not in house 2
        if assignment[1]['Car'] == 'chevrolet silverado':
            return False
            
        # Clue 3: Honda Civic and Peter are next to each other
        peter_pos = None
        honda_pos = None
        for i in range(6):
            if assignment[i]['Name'] == 'Peter':
                peter_pos = i
            if assignment[i]['Car'] == 'honda civic':
                honda_pos = i
        if abs(peter_pos - honda_pos) != 1:
            return False
            
        # Clue 4: Lawyer not in house 5
        if assignment[4]['Occupation'] == 'lawyer':
            return False
            
        # Clue 5: Nurse is directly left of artist
        nurse_pos = None
        artist_pos = None
        for i in range(6):
            if assignment[i]['Occupation'] == 'nurse':
                nurse_pos = i
            if assignment[i]['Occupation'] == 'artist':
                artist_pos = i
        if artist_pos != nurse_pos + 1:
            return False
            
        # Clue 6: Carol is right of Eric
        eric_pos = None
        carol_pos = None
        for i in range(6):
            if assignment[i]['Name'] == 'Eric':
                eric_pos = i
            if assignment[i]['Name'] == 'Carol':
                carol_pos = i
        if carol_pos <= eric_pos:
            return False
            
        # Clue 7: Doctor is Eric
        if assignment[eric_pos]['Occupation'] != 'doctor':
            return False
            
        # Clue 8: Teacher is left of nurse
        teacher_pos = None
        for i in range(6):
            if assignment[i]['Occupation'] == 'teacher':
                teacher_pos = i
        if teacher_pos >= nurse_pos:
            return False
            
        # Clue 9: Carol not in house 6
        if assignment[5]['Name'] == 'Carol':
            return False
            
        # Clue 10: Engineer is Bob
        bob_pos = None
        for i in range(6):
            if assignment[i]['Name'] == 'Bob':
                bob_pos = i
        if assignment[bob_pos]['Occupation'] != 'engineer':
            return False
            
        # Clue 11: Toyota Camry is nurse
        if assignment[nurse_pos]['Car'] != 'toyota camry':
            return False
            
        # Clue 12: One house between Peter and lawyer
        lawyer_pos = None
        for i in range(6):
            if assignment[i]['Occupation'] == 'lawyer':
                lawyer_pos = i
        if abs(peter_pos - lawyer_pos) != 2:
            return False
            
        # Clue 13: One house between Tesla and Bob
        tesla_pos = None
        for i in range(6):
            if assignment[i]['Car'] == 'tesla model 3':
                tesla_pos = i
        if abs(tesla_pos - bob_pos) != 2:
            return False
            
        # Clue 14: Artist is Arnold
        arnold_pos = None
        for i in range(6):
            if assignment[i]['Name'] == 'Arnold':
                arnold_pos = i
        if assignment[arnold_pos]['Occupation'] != 'artist':
            return False
            
        return True
    
    # Start the backtracking
    initial_assignment = [{'House': str(i+1)} for i in range(6)]
    solution = backtrack(initial_assignment, set(names), set(occupations), set(cars), 0)
    
    if solution is None:
        return {"solution": {"header": [], "rows": []}}
    
    # Prepare the output
    header = ["House", "Name", "Occupation", "Car"]
    rows = []
    for house in solution:
        row = [
            house['House'],
            house['Name'],
            house['Occupation'],
            house['Car']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

# Solve and print the puzzle
solution = solve_puzzle()
print(json.dumps(solution, indent=2))