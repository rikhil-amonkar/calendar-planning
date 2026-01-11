import json
from itertools import permutations

def solve():
    # Define all possible values for each category
    names = ["Peter", "Arnold", "Eric"]
    cars = ["toyota camry", "ford f150", "tesla model 3"]
    styles = ["ranch", "colonial", "victorian"]
    pets = ["cat", "dog", "fish"]
    occupations = ["engineer", "doctor", "teacher"]
    vacations = ["city", "mountain", "beach"]
    
    houses = [1, 2, 3]
    
    # Generate all permutations for each category
    all_names = list(permutations(names, 3))
    all_cars = list(permutations(cars, 3))
    all_styles = list(permutations(styles, 3))
    all_pets = list(permutations(pets, 3))
    all_occupations = list(permutations(occupations, 3))
    all_vacations = list(permutations(vacations, 3))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_perm in all_names:
        for car_perm in all_cars:
            for style_perm in all_styles:
                for pet_perm in all_pets:
                    for occ_perm in all_occupations:
                        for vac_perm in all_vacations:
                            # Build assignment for each house
                            assignment = []
                            for i in range(3):
                                assignment.append({
                                    'house': i+1,
                                    'name': name_perm[i],
                                    'car': car_perm[i],
                                    'style': style_perm[i],
                                    'pet': pet_perm[i],
                                    'occupation': occ_perm[i],
                                    'vacation': vac_perm[i]
                                })
                            
                            # Check all clues
                            valid = True
                            
                            # Clue 1: Fish in first house
                            if assignment[0]['pet'] != 'fish':
                                valid = False
                                continue
                            
                            # Clue 2: Toyota Camry in second house
                            if assignment[1]['car'] != 'toyota camry':
                                valid = False
                                continue
                            
                            # Clue 3: Mountain retreat not in second house
                            if assignment[1]['vacation'] == 'mountain':
                                valid = False
                                continue
                            
                            # Clue 4: City breaks not in second house
                            if assignment[1]['vacation'] == 'city':
                                valid = False
                                continue
                            
                            # Clue 5: Ranch-style home is somewhere to the left of Peter
                            ranch_index = None
                            peter_index = None
                            for i in range(3):
                                if assignment[i]['style'] == 'ranch':
                                    ranch_index = i
                                if assignment[i]['name'] == 'Peter':
                                    peter_index = i
                            if ranch_index is None or peter_index is None or ranch_index >= peter_index:
                                valid = False
                                continue
                            
                            # Clue 6: Toyota Camry is directly left of colonial-style house
                            camry_index = None
                            colonial_index = None
                            for i in range(3):
                                if assignment[i]['car'] == 'toyota camry':
                                    camry_index = i
                                if assignment[i]['style'] == 'colonial':
                                    colonial_index = i
                            if camry_index is None or colonial_index is None or colonial_index - camry_index != 1:
                                valid = False
                                continue
                            
                            # Clue 7: Arnold has a cat
                            arnold_index = None
                            for i in range(3):
                                if assignment[i]['name'] == 'Arnold':
                                    arnold_index = i
                                    break
                            if arnold_index is None or assignment[arnold_index]['pet'] != 'cat':
                                valid = False
                                continue
                            
                            # Clue 8: Eric is somewhere to the left of mountain retreats
                            eric_index = None
                            mountain_index = None
                            for i in range(3):
                                if assignment[i]['name'] == 'Eric':
                                    eric_index = i
                                if assignment[i]['vacation'] == 'mountain':
                                    mountain_index = i
                            if eric_index is None or mountain_index is None or eric_index >= mountain_index:
                                valid = False
                                continue
                            
                            # Clue 9: Engineer is not in third house
                            if assignment[2]['occupation'] == 'engineer':
                                valid = False
                                continue
                            
                            # Clue 10: Tesla Model 3 is somewhere to the left of teacher
                            tesla_index = None
                            teacher_index = None
                            for i in range(3):
                                if assignment[i]['car'] == 'tesla model 3':
                                    tesla_index = i
                                if assignment[i]['occupation'] == 'teacher':
                                    teacher_index = i
                            if tesla_index is None or teacher_index is None or tesla_index >= teacher_index:
                                valid = False
                                continue
                            
                            # Clue 11: Dog owner is the engineer
                            dog_index = None
                            engineer_index = None
                            for i in range(3):
                                if assignment[i]['pet'] == 'dog':
                                    dog_index = i
                                if assignment[i]['occupation'] == 'engineer':
                                    engineer_index = i
                            if dog_index is None or engineer_index is None or dog_index != engineer_index:
                                valid = False
                                continue
                            
                            # All clues satisfied
                            if valid:
                                solutions.append(assignment)
    
    # Format the solution
    if solutions:
        # Take the first valid solution
        solution = solutions[0]
        
        # Sort by house number
        solution.sort(key=lambda x: x['house'])
        
        # Build rows
        rows = []
        for house in solution:
            rows.append([
                str(house['house']),
                house['name'],
                house['car'],
                house['style'],
                house['pet'],
                house['occupation'],
                house['vacation']
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                "rows": rows
            }
        }
        
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve())