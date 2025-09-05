import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
    car_models = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
    phone_models = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
    occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
    drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all permutations for each category
    for name_perm in permutations(names):
        for food_perm in permutations(foods):
            for car_perm in permutations(car_models):
                for phone_perm in permutations(phone_models):
                    for occ_perm in permutations(occupations):
                        for drink_perm in permutations(drinks):
                            # Create assignment for each house
                            assignment = {}
                            for i, house in enumerate(houses):
                                assignment[house] = {
                                    'Name': name_perm[i],
                                    'Food': food_perm[i],
                                    'CarModel': car_perm[i],
                                    'PhoneModel': phone_perm[i],
                                    'Occupation': occ_perm[i],
                                    'Drink': drink_perm[i]
                                }
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The root beer lover is the person who owns a Honda Civic.
                            for house in houses:
                                if assignment[house]['Drink'] == 'root beer':
                                    if assignment[house]['CarModel'] != 'honda civic':
                                        valid = False
                                        break
                                if assignment[house]['CarModel'] == 'honda civic':
                                    if assignment[house]['Drink'] != 'root beer':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 2: The person who likes milk is directly left of the person who loves eating grilled cheese.
                            milk_house = None
                            grilled_cheese_house = None
                            for house in houses:
                                if assignment[house]['Drink'] == 'milk':
                                    milk_house = house
                                if assignment[house]['Food'] == 'grilled cheese':
                                    grilled_cheese_house = house
                            
                            if milk_house is None or grilled_cheese_house is None or milk_house + 1 != grilled_cheese_house:
                                valid = False
                                continue
                            
                            # Clue 3: Alice is the person who uses a Samsung Galaxy S21.
                            for house in houses:
                                if assignment[house]['Name'] == 'Alice':
                                    if assignment[house]['PhoneModel'] != 'samsung galaxy s21':
                                        valid = False
                                        break
                                if assignment[house]['PhoneModel'] == 'samsung galaxy s21':
                                    if assignment[house]['Name'] != 'Alice':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 4: Alice is the person who loves stir fry.
                            for house in houses:
                                if assignment[house]['Name'] == 'Alice':
                                    if assignment[house]['Food'] != 'stir fry':
                                        valid = False
                                        break
                                if assignment[house]['Food'] == 'stir fry':
                                    if assignment[house]['Name'] != 'Alice':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 5: The tea drinker is not in the fifth house.
                            if assignment[5]['Drink'] == 'tea':
                                valid = False
                                continue
                            
                            # Clue 6: The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
                            bmw_house = None
                            tea_house = None
                            for house in houses:
                                if assignment[house]['CarModel'] == 'bmw 3 series':
                                    bmw_house = house
                                if assignment[house]['Drink'] == 'tea':
                                    tea_house = house
                            
                            if bmw_house is None or tea_house is None or bmw_house >= tea_house:
                                valid = False
                                continue
                            
                            # Clue 7: The person who is a doctor is Arnold.
                            for house in houses:
                                if assignment[house]['Occupation'] == 'doctor':
                                    if assignment[house]['Name'] != 'Arnold':
                                        valid = False
                                        break
                                if assignment[house]['Name'] == 'Arnold':
                                    if assignment[house]['Occupation'] != 'doctor':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 8: The person who uses an iPhone 13 is the coffee drinker.
                            for house in houses:
                                if assignment[house]['PhoneModel'] == 'iphone 13':
                                    if assignment[house]['Drink'] != 'coffee':
                                        valid = False
                                        break
                                if assignment[house]['Drink'] == 'coffee':
                                    if assignment[house]['PhoneModel'] != 'iphone 13':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 9: The person who is an engineer is the person who owns a BMW 3 Series.
                            for house in houses:
                                if assignment[house]['Occupation'] == 'engineer':
                                    if assignment[house]['CarModel'] != 'bmw 3 series':
                                        valid = False
                                        break
                                if assignment[house]['CarModel'] == 'bmw 3 series':
                                    if assignment[house]['Occupation'] != 'engineer':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 10: The person who loves the stew is the person who uses an iPhone 13.
                            for house in houses:
                                if assignment[house]['Food'] == 'stew':
                                    if assignment[house]['PhoneModel'] != 'iphone 13':
                                        valid = False
                                        break
                                if assignment[house]['PhoneModel'] == 'iphone 13':
                                    if assignment[house]['Food'] != 'stew':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 11: The person who is a doctor is directly left of the person who uses a OnePlus 9.
                            doctor_house = None
                            oneplus_house = None
                            for house in houses:
                                if assignment[house]['Occupation'] == 'doctor':
                                    doctor_house = house
                                if assignment[house]['PhoneModel'] == 'oneplus 9':
                                    oneplus_house = house
                            
                            if doctor_house is None or oneplus_house is None or doctor_house + 1 != oneplus_house:
                                valid = False
                                continue
                            
                            # Clue 12: The person who owns a Honda Civic is directly left of the person who loves the spaghetti eater.
                            honda_house = None
                            spaghetti_house = None
                            for house in houses:
                                if assignment[house]['CarModel'] == 'honda civic':
                                    honda_house = house
                                if assignment[house]['Food'] == 'spaghetti':
                                    spaghetti_house = house
                            
                            if honda_house is None or spaghetti_house is None or honda_house + 1 != spaghetti_house:
                                valid = False
                                continue
                            
                            # Clue 13: The person who uses a Google Pixel 6 is the tea drinker.
                            for house in houses:
                                if assignment[house]['PhoneModel'] == 'google pixel 6':
                                    if assignment[house]['Drink'] != 'tea':
                                        valid = False
                                        break
                                if assignment[house]['Drink'] == 'tea':
                                    if assignment[house]['PhoneModel'] != 'google pixel 6':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 14: Alice is the person who is an artist.
                            for house in houses:
                                if assignment[house]['Name'] == 'Alice':
                                    if assignment[house]['Occupation'] != 'artist':
                                        valid = False
                                        break
                                if assignment[house]['Occupation'] == 'artist':
                                    if assignment[house]['Name'] != 'Alice':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 15: There is one house between Alice and the person who owns a Ford F-150.
                            alice_house = None
                            ford_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Alice':
                                    alice_house = house
                                if assignment[house]['CarModel'] == 'ford f150':
                                    ford_house = house
                            
                            if alice_house is None or ford_house is None or abs(alice_house - ford_house) != 2:
                                valid = False
                                continue
                            
                            # Clue 16: Arnold is the person who owns a Toyota Camry.
                            for house in houses:
                                if assignment[house]['Name'] == 'Arnold':
                                    if assignment[house]['CarModel'] != 'toyota camry':
                                        valid = False
                                        break
                                if assignment[house]['CarModel'] == 'toyota camry':
                                    if assignment[house]['Name'] != 'Arnold':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 17: Eric is in the fourth house.
                            if assignment[4]['Name'] != 'Eric':
                                valid = False
                                continue
                            
                            # Clue 18: The person who uses a OnePlus 9 is the person who is a lawyer.
                            for house in houses:
                                if assignment[house]['PhoneModel'] == 'oneplus 9':
                                    if assignment[house]['Occupation'] != 'lawyer':
                                        valid = False
                                        break
                                if assignment[house]['Occupation'] == 'lawyer':
                                    if assignment[house]['PhoneModel'] != 'oneplus 9':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 19: The person who loves eating grilled cheese is Peter.
                            for house in houses:
                                if assignment[house]['Food'] == 'grilled cheese':
                                    if assignment[house]['Name'] != 'Peter':
                                        valid = False
                                        break
                                if assignment[house]['Name'] == 'Peter':
                                    if assignment[house]['Food'] != 'grilled cheese':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # If we reach here, all constraints are satisfied
                            if valid:
                                # Format the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                                        "rows": []
                                    }
                                }
                                
                                for house in sorted(assignment.keys()):
                                    row = [
                                        str(house),
                                        assignment[house]['Name'],
                                        assignment[house]['Food'],
                                        assignment[house]['CarModel'],
                                        assignment[house]['PhoneModel'],
                                        assignment[house]['Occupation'],
                                        assignment[house]['Drink']
                                    ]
                                    solution["solution"]["rows"].append(row)
                                
                                print(json.dumps(solution, indent=2))
                                return
    
    print("No solution found")

if __name__ == "__main__":
    main()