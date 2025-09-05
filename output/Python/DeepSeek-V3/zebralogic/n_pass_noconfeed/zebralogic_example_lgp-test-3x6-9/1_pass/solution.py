import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Peter', 'Arnold', 'Eric']
    car_models = ['toyota camry', 'ford f150', 'tesla model 3']
    house_styles = ['ranch', 'colonial', 'victorian']
    pets = ['cat', 'dog', 'fish']
    occupations = ['engineer', 'doctor', 'teacher']
    vacations = ['city', 'mountain', 'beach']
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for car_perm in permutations(car_models):
            for style_perm in permutations(house_styles):
                for pet_perm in permutations(pets):
                    for occ_perm in permutations(occupations):
                        for vac_perm in permutations(vacations):
                            # Create assignment for current permutation
                            assignment = {
                                1: {
                                    'Name': name_perm[0],
                                    'CarModel': car_perm[0],
                                    'HouseStyle': style_perm[0],
                                    'Pet': pet_perm[0],
                                    'Occupation': occ_perm[0],
                                    'Vacation': vac_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'CarModel': car_perm[1],
                                    'HouseStyle': style_perm[1],
                                    'Pet': pet_perm[1],
                                    'Occupation': occ_perm[1],
                                    'Vacation': vac_perm[1]
                                },
                                3: {
                                    'Name': name_perm[2],
                                    'CarModel': car_perm[2],
                                    'HouseStyle': style_perm[2],
                                    'Pet': pet_perm[2],
                                    'Occupation': occ_perm[2],
                                    'Vacation': vac_perm[2]
                                }
                            }
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The person with an aquarium of fish is in the first house.
                            if assignment[1]['Pet'] != 'fish':
                                valid = False
                                continue
                            
                            # Clue 2: The person who owns a Toyota Camry is in the second house.
                            if assignment[2]['CarModel'] != 'toyota camry':
                                valid = False
                                continue
                            
                            # Clue 3: The person who enjoys mountain retreats is not in the second house.
                            if assignment[2]['Vacation'] == 'mountain':
                                valid = False
                                continue
                            
                            # Clue 4: The person who prefers city breaks is not in the second house.
                            if assignment[2]['Vacation'] == 'city':
                                valid = False
                                continue
                            
                            # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
                            peter_house = None
                            ranch_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Peter':
                                    peter_house = house
                                if assignment[house]['HouseStyle'] == 'ranch':
                                    ranch_house = house
                            
                            if peter_house is None or ranch_house is None or ranch_house >= peter_house:
                                valid = False
                                continue
                            
                            # Clue 6: The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
                            # Toyota Camry is in house 2 (from clue 2), so colonial must be in house 3
                            if assignment[3]['HouseStyle'] != 'colonial':
                                valid = False
                                continue
                            
                            # Clue 7: Arnold is the person who has a cat.
                            for house in houses:
                                if assignment[house]['Name'] == 'Arnold' and assignment[house]['Pet'] != 'cat':
                                    valid = False
                                    break
                                if assignment[house]['Pet'] == 'cat' and assignment[house]['Name'] != 'Arnold':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
                            eric_house = None
                            mountain_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Eric':
                                    eric_house = house
                                if assignment[house]['Vacation'] == 'mountain':
                                    mountain_house = house
                            
                            if eric_house is None or mountain_house is None or eric_house >= mountain_house:
                                valid = False
                                continue
                            
                            # Clue 9: The person who is an engineer is not in the third house.
                            if assignment[3]['Occupation'] == 'engineer':
                                valid = False
                                continue
                            
                            # Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
                            tesla_house = None
                            teacher_house = None
                            for house in houses:
                                if assignment[house]['CarModel'] == 'tesla model 3':
                                    tesla_house = house
                                if assignment[house]['Occupation'] == 'teacher':
                                    teacher_house = house
                            
                            if tesla_house is None or teacher_house is None or tesla_house >= teacher_house:
                                valid = False
                                continue
                            
                            # Clue 11: The person who owns a dog is the person who is an engineer.
                            for house in houses:
                                if assignment[house]['Pet'] == 'dog' and assignment[house]['Occupation'] != 'engineer':
                                    valid = False
                                    break
                                if assignment[house]['Occupation'] == 'engineer' and assignment[house]['Pet'] != 'dog':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # If we get here, all constraints are satisfied
                            if valid:
                                # Format the solution as required
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                                        "rows": []
                                    }
                                }
                                
                                for house in sorted(assignment.keys()):
                                    row = [
                                        str(house),
                                        assignment[house]['Name'],
                                        assignment[house]['CarModel'],
                                        assignment[house]['HouseStyle'],
                                        assignment[house]['Pet'],
                                        assignment[house]['Occupation'],
                                        assignment[house]['Vacation']
                                    ]
                                    solution["solution"]["rows"].append(row)
                                
                                print(json.dumps(solution, indent=2))
                                return
    
    print("No solution found")

if __name__ == "__main__":
    main()