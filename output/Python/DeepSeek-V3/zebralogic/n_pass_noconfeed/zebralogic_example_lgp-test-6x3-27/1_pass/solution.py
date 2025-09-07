import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    car_models = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']
    
    # Generate all possible permutations for names, occupations, and car models
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for car_perm in permutations(car_models):
                # Assign each permutation to houses 1-6
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'name': name_perm[i],
                        'occupation': occ_perm[i],
                        'car': car_perm[i]
                    }
                
                # Check all constraints
                # Clue 1: The person who owns a Ford F-150 is in the fifth house.
                if assignment[5]['car'] != 'ford f150':
                    continue
                
                # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
                if assignment[2]['car'] == 'chevrolet silverado':
                    continue
                
                # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
                honda_civic_house = None
                peter_house = None
                for house in houses:
                    if assignment[house]['car'] == 'honda civic':
                        honda_civic_house = house
                    if assignment[house]['name'] == 'Peter':
                        peter_house = house
                if honda_civic_house is None or peter_house is None or abs(honda_civic_house - peter_house) != 1:
                    continue
                
                # Clue 4: The person who is a lawyer is not in the fifth house.
                if assignment[5]['occupation'] == 'lawyer':
                    continue
                
                # Clue 5: The person who is a nurse is directly left of the person who is an artist.
                nurse_house = None
                artist_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'nurse':
                        nurse_house = house
                    if assignment[house]['occupation'] == 'artist':
                        artist_house = house
                if nurse_house is None or artist_house is None or artist_house - nurse_house != 1:
                    continue
                
                # Clue 6: Carol is somewhere to the right of Eric.
                carol_house = None
                eric_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Carol':
                        carol_house = house
                    if assignment[house]['name'] == 'Eric':
                        eric_house = house
                if carol_house is None or eric_house is None or carol_house <= eric_house:
                    continue
                
                # Clue 7: The person who is a doctor is Eric.
                doctor_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'doctor':
                        doctor_house = house
                if doctor_house is None or assignment[doctor_house]['name'] != 'Eric':
                    continue
                
                # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
                teacher_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'teacher':
                        teacher_house = house
                if teacher_house is None or nurse_house is None or teacher_house >= nurse_house:
                    continue
                
                # Clue 9: Carol is not in the sixth house.
                if assignment[6]['name'] == 'Carol':
                    continue
                
                # Clue 10: The person who is an engineer is Bob.
                engineer_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'engineer':
                        engineer_house = house
                if engineer_house is None or assignment[engineer_house]['name'] != 'Bob':
                    continue
                
                # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
                if assignment[nurse_house]['car'] != 'toyota camry':
                    continue
                
                # Clue 12: There is one house between Peter and the person who is a lawyer.
                lawyer_house = None
                for house in houses:
                    if assignment[house]['occupation'] == 'lawyer':
                        lawyer_house = house
                if lawyer_house is None or abs(peter_house - lawyer_house) != 2:
                    continue
                
                # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
                tesla_house = None
                bob_house = None
                for house in houses:
                    if assignment[house]['car'] == 'tesla model 3':
                        tesla_house = house
                    if assignment[house]['name'] == 'Bob':
                        bob_house = house
                if tesla_house is None or bob_house is None or abs(tesla_house - bob_house) != 2:
                    continue
                
                # Clue 14: Arnold is the person who is an artist.
                if assignment[artist_house]['name'] != 'Arnold':
                    continue
                
                # If all constraints are satisfied, format the solution
                solution = {
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
                    solution["solution"]["rows"].append(row)
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return
    
    # If no solution found
    print(json.dumps({"solution": {"header": ["House", "Name", "Occupation", "CarModel"], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()