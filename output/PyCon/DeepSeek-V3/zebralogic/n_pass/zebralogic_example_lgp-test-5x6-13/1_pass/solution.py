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
    
    # Add variables for each attribute
    problem.addVariable('name', names)
    problem.addVariable('food', foods)
    problem.addVariable('car', cars)
    problem.addVariable('phone', phones)
    problem.addVariable('occupation', occupations)
    problem.addVariable('drink', drinks)
    
    # All variables must have different values (all attributes are unique)
    problem.addConstraint(constraint.AllDifferentConstraint(), ['name'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['food'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['car'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['phone'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['occupation'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['drink'])
    
    # Clue 1: The root beer lover is the person who owns a Honda Civic.
    problem.addConstraint(lambda drink, car: (drink == 'root beer') == (car == 'honda civic'), ['drink', 'car'])
    
    # Clue 2: The person who likes milk is directly left of the person who loves eating grilled cheese.
    problem.addConstraint(lambda milk_house, gc_house: milk_house + 1 == gc_house if milk_house is not None and gc_house is not None else False, 
                         [f"drink_milk_house", f"food_gc_house"])
    
    # Clue 3: Alice is the person who uses a Samsung Galaxy S21.
    problem.addConstraint(lambda name, phone: not (name == 'Alice') or (phone == 'samsung galaxy s21'), ['name', 'phone'])
    
    # Clue 4: Alice is the person who loves stir fry.
    problem.addConstraint(lambda name, food: not (name == 'Alice') or (food == 'stir fry'), ['name', 'food'])
    
    # Clue 5: The tea drinker is not in the fifth house.
    problem.addConstraint(lambda drink, house: not (drink == 'tea') or (house != 5), ['drink', 'house'])
    
    # Clue 6: The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
    problem.addConstraint(lambda bmw_house, tea_house: bmw_house < tea_house if bmw_house is not None and tea_house is not None else False,
                         [f"car_bmw_house", f"drink_tea_house"])
    
    # Clue 7: The person who is a doctor is Arnold.
    problem.addConstraint(lambda occupation, name: not (occupation == 'doctor') or (name == 'Arnold'), ['occupation', 'name'])
    
    # Clue 8: The person who uses an iPhone 13 is the coffee drinker.
    problem.addConstraint(lambda phone, drink: (phone == 'iphone 13') == (drink == 'coffee'), ['phone', 'drink'])
    
    # Clue 9: The person who is an engineer is the person who owns a BMW 3 Series.
    problem.addConstraint(lambda occupation, car: (occupation == 'engineer') == (car == 'bmw 3 series'), ['occupation', 'car'])
    
    # Clue 10: The person who loves the stew is the person who uses an iPhone 13.
    problem.addConstraint(lambda food, phone: (food == 'stew') == (phone == 'iphone 13'), ['food', 'phone'])
    
    # Clue 11: The person who is a doctor is directly left of the person who uses a OnePlus 9.
    problem.addConstraint(lambda doc_house, op9_house: doc_house + 1 == op9_house if doc_house is not None and op9_house is not None else False,
                         [f"occupation_doc_house", f"phone_op9_house"])
    
    # Clue 12: The person who owns a Honda Civic is directly left of the person who loves the spaghetti eater.
    problem.addConstraint(lambda civic_house, spaghetti_house: civic_house + 1 == spaghetti_house if civic_house is not None and spaghetti_house is not None else False,
                         [f"car_civic_house", f"food_spaghetti_house"])
    
    # Clue 13: The person who uses a Google Pixel 6 is the tea drinker.
    problem.addConstraint(lambda phone, drink: (phone == 'google pixel 6') == (drink == 'tea'), ['phone', 'drink'])
    
    # Clue 14: Alice is the person who is an artist.
    problem.addConstraint(lambda name, occupation: not (name == 'Alice') or (occupation == 'artist'), ['name', 'occupation'])
    
    # Clue 15: There is one house between Alice and the person who owns a Ford F-150.
    problem.addConstraint(lambda alice_house, f150_house: abs(alice_house - f150_house) == 2 if alice_house is not None and f150_house is not None else False,
                         [f"name_alice_house", f"car_f150_house"])
    
    # Clue 16: Arnold is the person who owns a Toyota Camry.
    problem.addConstraint(lambda name, car: not (name == 'Arnold') or (car == 'toyota camry'), ['name', 'car'])
    
    # Clue 17: Eric is in the fourth house.
    problem.addConstraint(lambda name, house: not (name == 'Eric') or (house == 4), ['name', 'house'])
    
    # Clue 18: The person who uses a OnePlus 9 is the person who is a lawyer.
    problem.addConstraint(lambda phone, occupation: (phone == 'oneplus 9') == (occupation == 'lawyer'), ['phone', 'occupation'])
    
    # Clue 19: The person who loves eating grilled cheese is Peter.
    problem.addConstraint(lambda food, name: not (food == 'grilled cheese') or (name == 'Peter'), ['food', 'name'])
    
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
    
    # Add constraints that link the single variables with house variables
    for house in houses:
        problem.addConstraint(lambda name, name_h=house: name == name_h, [f'name_{house}', 'name'])
        problem.addConstraint(lambda food, food_h=house: food == food_h, [f'food_{house}', 'food'])
        problem.addConstraint(lambda car, car_h=house: car == car_h, [f'car_{house}', 'car'])
        problem.addConstraint(lambda phone, phone_h=house: phone == phone_h, [f'phone_{house}', 'phone'])
        problem.addConstraint(lambda occupation, occupation_h=house: occupation == occupation_h, [f'occupation_{house}', 'occupation'])
        problem.addConstraint(lambda drink, drink_h=house: drink == drink_h, [f'drink_{house}', 'drink'])
    
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