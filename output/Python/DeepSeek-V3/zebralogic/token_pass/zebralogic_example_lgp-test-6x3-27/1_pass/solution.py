import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]
    
    # Generate all permutations
    for name_perm in permutations(names, 6):
        for occ_perm in permutations(occupations, 6):
            for car_perm in permutations(cars, 6):
                # Create assignment dictionaries
                assignment = {}
                for i in range(6):
                    house = i + 1
                    assignment[house] = {
                        'name': name_perm[i],
                        'occupation': occ_perm[i],
                        'car': car_perm[i]
                    }
                
                # Check all clues
                # 1. Ford F-150 is in the fifth house
                if assignment[5]['car'] != 'ford f150':
                    continue
                
                # 2. Chevrolet Silverado is not in the second house
                if assignment[2]['car'] == 'chevrolet silverado':
                    continue
                
                # 3. Honda Civic and Peter are next to each other
                honda_house = None
                peter_house = None
                for house in houses:
                    if assignment[house]['car'] == 'honda civic':
                        honda_house = house
                    if assignment[house]['name'] == 'Peter':
                        peter_house = house
                if abs(honda_house - peter_house) != 1:
                    continue
                
                # 4. Lawyer is not in the fifth house
                if assignment[5]['occupation'] == 'lawyer':
                    continue
                
                # 5. Nurse is directly left of artist
                nurse_house = None
                artist_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'nurse':
                        nurse_house = house
                    if assignment[house]['occupation'] == 'artist':
                        artist_house = house
                if artist_house - nurse_house != 1:
                    continue
                
                # 6. Carol is somewhere to the right of Eric
                carol_house = None
                eric_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Carol':
                        carol_house = house
                    if assignment[house]['name'] == 'Eric':
                        eric_house = house
                if not (carol_house > eric_house):
                    continue
                
                # 7. Doctor is Eric
                if assignment[eric_house]['occupation'] != 'doctor':
                    continue
                
                # 8. Teacher is somewhere to the left of nurse
                teacher_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'teacher':
                        teacher_house = house
                        break
                if not (teacher_house < nurse_house):
                    continue
                
                # 9. Carol is not in the sixth house
                if assignment[6]['name'] == 'Carol':
                    continue
                
                # 10. Engineer is Bob
                bob_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Bob':
                        bob_house = house
                        break
                if assignment[bob_house]['occupation'] != 'engineer':
                    continue
                
                # 11. Toyota Camry is the nurse
                if assignment[nurse_house]['car'] != 'toyota camry':
                    continue
                
                # 12. One house between Peter and lawyer
                lawyer_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'lawyer':
                        lawyer_house = house
                        break
                if abs(peter_house - lawyer_house) != 2:
                    continue
                
                # 13. One house between Tesla Model 3 and Bob
                tesla_house = None
                for house in houses:
                    if assignment[house]['car'] == 'tesla model 3':
                        tesla_house = house
                        break
                if abs(tesla_house - bob_house) != 2:
                    continue
                
                # 14. Arnold is the artist
                arnold_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Arnold':
                        arnold_house = house
                        break
                if assignment[arnold_house]['occupation'] != 'artist':
                    continue
                
                # All constraints satisfied - found solution
                result = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "CarModel"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment.keys()):
                    row = [
                        str(house),
                        assignment[house]['name'],
                        assignment[house]['occupation'],
                        assignment[house]['car']
                    ]
                    result["solution"]["rows"].append(row)
                
                return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()