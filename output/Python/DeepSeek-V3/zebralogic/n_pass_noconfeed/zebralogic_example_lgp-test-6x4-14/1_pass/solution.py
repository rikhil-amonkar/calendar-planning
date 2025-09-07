import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    car_models = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for car_perm in permutations(car_models):
            for mother_perm in permutations(mothers):
                for hobby_perm in permutations(hobbies):
                    # Create assignment dictionaries for each house
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'Name': name_perm[i],
                            'CarModel': car_perm[i],
                            'Mother': mother_perm[i],
                            'Hobby': hobby_perm[i]
                        }
                    
                    # Check all constraints
                    # Clue 1: The person who owns a Toyota Camry is in the sixth house.
                    if assignment[6]['CarModel'] != 'toyota camry':
                        continue
                    
                    # Clue 2: Carol is the photography enthusiast.
                    carol_house = None
                    for house, attrs in assignment.items():
                        if attrs['Name'] == 'Carol':
                            carol_house = house
                            break
                    if carol_house is None or assignment[carol_house]['Hobby'] != 'photography':
                        continue
                    
                    # Clue 3: The person who owns a Chevrolet Silverado is The person whose mother's name is Aniya.
                    silverado_house = None
                    aniya_house = None
                    for house, attrs in assignment.items():
                        if attrs['CarModel'] == 'chevrolet silverado':
                            silverado_house = house
                        if attrs['Mother'] == 'Aniya':
                            aniya_house = house
                    if silverado_house != aniya_house:
                        continue
                    
                    # Clue 4: The person who owns a Chevrolet Silverado is not in the second house.
                    if silverado_house == 2:
                        continue
                    
                    # Clue 5: The person who owns a Ford F-150 is The person whose mother's name is Sarah.
                    f150_house = None
                    sarah_house = None
                    for house, attrs in assignment.items():
                        if attrs['CarModel'] == 'ford f150':
                            f150_house = house
                        if attrs['Mother'] == 'Sarah':
                            sarah_house = house
                    if f150_house != sarah_house:
                        continue
                    
                    # Clue 6: The person who owns a BMW 3 Series is Bob.
                    bmw_house = None
                    bob_house = None
                    for house, attrs in assignment.items():
                        if attrs['CarModel'] == 'bmw 3 series':
                            bmw_house = house
                        if attrs['Name'] == 'Bob':
                            bob_house = house
                    if bmw_house != bob_house:
                        continue
                    
                    # Clue 7: The person whose mother's name is Kailyn is in the sixth house.
                    if assignment[6]['Mother'] != 'Kailyn':
                        continue
                    
                    # Clue 8: Eric is directly left of the person who enjoys knitting.
                    eric_house = None
                    knitting_house = None
                    for house, attrs in assignment.items():
                        if attrs['Name'] == 'Eric':
                            eric_house = house
                        if attrs['Hobby'] == 'knitting':
                            knitting_house = house
                    if eric_house is None or knitting_house is None or knitting_house - eric_house != 1:
                        continue
                    
                    # Clue 9: There is one house between The person whose mother's name is Sarah and the person who owns a Toyota Camry.
                    if sarah_house is None or abs(sarah_house - 6) != 2:
                        continue
                    
                    # Clue 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
                    penny_house = None
                    for house, attrs in assignment.items():
                        if attrs['Mother'] == 'Penny':
                            penny_house = house
                            break
                    if penny_house is None or penny_house <= knitting_house:
                        continue
                    
                    # Clue 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
                    honda_house = None
                    for house, attrs in assignment.items():
                        if attrs['CarModel'] == 'honda civic':
                            honda_house = house
                            break
                    if aniya_house is None or honda_house is None or aniya_house <= honda_house:
                        continue
                    
                    # Clue 12: Alice is somewhere to the right of the person who owns a Ford F-150.
                    alice_house = None
                    for house, attrs in assignment.items():
                        if attrs['Name'] == 'Alice':
                            alice_house = house
                            break
                    if alice_house is None or f150_house is None or alice_house <= f150_house:
                        continue
                    
                    # Clue 13: Eric is the person who enjoys gardening.
                    if assignment[eric_house]['Hobby'] != 'gardening':
                        continue
                    
                    # Clue 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
                    woodworking_house = None
                    for house, attrs in assignment.items():
                        if attrs['Hobby'] == 'woodworking':
                            woodworking_house = house
                            break
                    if woodworking_house is None or woodworking_house >= knitting_house:
                        continue
                    
                    # Clue 15: There is one house between The person whose mother's name is Sarah and the person who loves cooking.
                    cooking_house = None
                    for house, attrs in assignment.items():
                        if attrs['Hobby'] == 'cooking':
                            cooking_house = house
                            break
                    if cooking_house is None or abs(sarah_house - cooking_house) != 2:
                        continue
                    
                    # Clue 16: The person who owns a Honda Civic is Arnold.
                    if assignment[honda_house]['Name'] != 'Arnold':
                        continue
                    
                    # Clue 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
                    holly_house = None
                    for house, attrs in assignment.items():
                        if attrs['Mother'] == 'Holly':
                            holly_house = house
                            break
                    if holly_house is None or knitting_house - holly_house != 1:
                        continue
                    
                    # If we reach here, all constraints are satisfied
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        attrs = assignment[house]
                        solution["solution"]["rows"].append([
                            str(house),
                            attrs['Name'],
                            attrs['CarModel'],
                            attrs['Mother'],
                            attrs['Hobby']
                        ])
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()