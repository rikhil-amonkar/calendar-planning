import constraint
import json

def solve_puzzle():
    problem = constraint.Problem()
    
    houses = [1, 2, 3, 4, 5]
    
    # Define variables
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
    cars = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
    phones = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
    occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
    drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']
    
    # Create variables for house positions
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'food_{house}', foods)
        problem.addVariable(f'car_{house}', cars)
        problem.addVariable(f'phone_{house}', phones)
        problem.addVariable(f'occupation_{house}', occupations)
        problem.addVariable(f'drink_{house}', drinks)
    
    # All houses must have different values for each attribute
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'name_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'food_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'car_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'phone_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'occupation_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'drink_{h}' for h in houses])
    
    # Clue 1: The root beer lover is the person who owns a Honda Civic.
    for house in houses:
        problem.addConstraint(
            lambda drink, car, h=house: not ((drink == 'root beer') and (car != 'honda civic')) and 
                                       not ((drink != 'root beer') and (car == 'honda civic')),
            [f'drink_{house}', f'car_{house}']
        )
    
    # Clue 2: The person who likes milk is directly left of the person who loves eating grilled cheese.
    for i in range(1, 5):  # Houses 1-4 can be left of another house
        problem.addConstraint(
            lambda milk, gc: not (milk == 'milk') or (gc == 'grilled cheese'),
            [f'drink_{i}', f'food_{i+1}']
        )
    
    # Clue 3: Alice is the person who uses a Samsung Galaxy S21.
    for house in houses:
        problem.addConstraint(
            lambda name, phone, h=house: not (name == 'Alice') or (phone == 'samsung galaxy s21'),
            [f'name_{house}', f'phone_{house}']
        )
    
    # Clue 4: Alice is the person who loves stir fry.
    for house in houses:
        problem.addConstraint(
            lambda name, food, h=house: not (name == 'Alice') or (food == 'stir fry'),
            [f'name_{house}', f'food_{house}']
        )
    
    # Clue 5: The tea drinker is not in the fifth house.
    problem.addConstraint(
        lambda drink: drink != 'tea',
        [f'drink_5']
    )
    
    # Clue 6: The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
    def bmw_left_of_tea(*args):
        # args are: drink_1, car_1, drink_2, car_2, ..., drink_5, car_5
        bmw_houses = []
        tea_house = None
        
        for i in range(5):
            drink = args[i*2]
            car = args[i*2 + 1]
            if car == 'bmw 3 series':
                bmw_houses.append(i+1)
            if drink == 'tea':
                tea_house = i+1
        
        if tea_house is None or not bmw_houses:
            return True
            
        return any(bmw_house < tea_house for bmw_house in bmw_houses)
    
    all_drink_car = []
    for house in houses:
        all_drink_car.extend([f'drink_{house}', f'car_{house}'])
    problem.addConstraint(bmw_left_of_tea, all_drink_car)
    
    # Clue 7: The person who is a doctor is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda occupation, name, h=house: not (occupation == 'doctor') or (name == 'Arnold'),
            [f'occupation_{house}', f'name_{house}']
        )
    
    # Clue 8: The person who uses an iPhone 13 is the coffee drinker.
    for house in houses:
        problem.addConstraint(
            lambda phone, drink, h=house: not ((phone == 'iphone 13') and (drink != 'coffee')) and 
                                       not ((phone != 'iphone 13') and (drink == 'coffee')),
            [f'phone_{house}', f'drink_{house}']
        )
    
    # Clue 9: The person who is an engineer is the person who owns a BMW 3 Series.
    for house in houses:
        problem.addConstraint(
            lambda occupation, car, h=house: not ((occupation == 'engineer') and (car != 'bmw 3 series')) and 
                                           not ((occupation != 'engineer') and (car == 'bmw 3 series')),
            [f'occupation_{house}', f'car_{house}']
        )
    
    # Clue 10: The person who loves the stew is the person who uses an iPhone 13.
    for house in houses:
        problem.addConstraint(
            lambda food, phone, h=house: not ((food == 'stew') and (phone != 'iphone 13')) and 
                                       not ((food != 'stew') and (phone == 'iphone 13')),
            [f'food_{house}', f'phone_{house}']
        )
    
    # Clue 11: The person who is a doctor is directly left of the person who uses a OnePlus 9.
    for i in range(1, 5):
        problem.addConstraint(
            lambda occupation, phone: not (occupation == 'doctor') or (phone == 'oneplus 9'),
            [f'occupation_{i}', f'phone_{i+1}']
        )
    
    # Clue 12: The person who owns a Honda Civic is directly left of the person who loves the spaghetti eater.
    for i in range(1, 5):
        problem.addConstraint(
            lambda car, food: not (car == 'honda civic') or (food == 'spaghetti'),
            [f'car_{i}', f'food_{i+1}']
        )
    
    # Clue 13: The person who uses a Google Pixel 6 is the tea drinker.
    for house in houses:
        problem.addConstraint(
            lambda phone, drink, h=house: not ((phone == 'google pixel 6') and (drink != 'tea')) and 
                                       not ((phone != 'google pixel 6') and (drink == 'tea')),
            [f'phone_{house}', f'drink_{house}']
        )
    
    # Clue 14: Alice is the person who is an artist.
    for house in houses:
        problem.addConstraint(
            lambda name, occupation, h=house: not (name == 'Alice') or (occupation == 'artist'),
            [f'name_{house}', f'occupation_{house}']
        )
    
    # Clue 15: There is one house between Alice and the person who owns a Ford F-150.
    def alice_f150_distance(*args):
        # args are: name_1, car_1, name_2, car_2, ..., name_5, car_5
        alice_house = None
        f150_house = None
        
        for i in range(5):
            name = args[i*2]
            car = args[i*2 + 1]
            if name == 'Alice':
                alice_house = i+1
            if car == 'ford f150':
                f150_house = i+1
        
        if alice_house is None or f150_house is None:
            return True
            
        return abs(alice_house - f150_house) == 2
    
    all_name_car = []
    for house in houses:
        all_name_car.extend([f'name_{house}', f'car_{house}'])
    problem.addConstraint(alice_f150_distance, all_name_car)
    
    # Clue 16: Arnold is the person who owns a Toyota Camry.
    for house in houses:
        problem.addConstraint(
            lambda name, car, h=house: not (name == 'Arnold') or (car == 'toyota camry'),
            [f'name_{house}', f'car_{house}']
        )
    
    # Clue 17: Eric is in the fourth house.
    problem.addConstraint(
        lambda name: name == 'Eric',
        [f'name_4']
    )
    
    # Clue 18: The person who uses a OnePlus 9 is the person who is a lawyer.
    for house in houses:
        problem.addConstraint(
            lambda phone, occupation, h=house: not ((phone == 'oneplus 9') and (occupation != 'lawyer')) and 
                                           not ((phone != 'oneplus 9') and (occupation == 'lawyer')),
            [f'phone_{house}', f'occupation_{house}']
        )
    
    # Clue 19: The person who loves eating grilled cheese is Peter.
    for house in houses:
        problem.addConstraint(
            lambda food, name, h=house: not (food == 'grilled cheese') or (name == 'Peter'),
            [f'food_{house}', f'name_{house}']
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    result = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'food_{house}'],
            solution[f'car_{house}'],
            solution[f'phone_{house}'],
            solution[f'occupation_{house}'],
            solution[f'drink_{house}']
        ]
        result["solution"]["rows"].append(row)
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))