import json
from z3 import *

def main():
    # Define the attribute options
    names = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
    foods = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
    heights = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
    drinks = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
    pets = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
    phones = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']

    # Create solver
    s = Solver()

    # Create variables for each house and attribute
    name_vars = [Int(f'name_{i}') for i in range(6)]
    food_vars = [Int(f'food_{i}') for i in range(6)]
    height_vars = [Int(f'height_{i}') for i in range(6)]
    drink_vars = [Int(f'drink_{i}') for i in range(6)]
    pet_vars = [Int(f'pet_{i}') for i in range(6)]
    phone_vars = [Int(f'phone_{i}') for i in range(6)]

    # Add constraints for valid values (0-5)
    for i in range(6):
        s.add(name_vars[i] >= 0, name_vars[i] < 6)
        s.add(food_vars[i] >= 0, food_vars[i] < 6)
        s.add(height_vars[i] >= 0, height_vars[i] < 6)
        s.add(drink_vars[i] >= 0, drink_vars[i] < 6)
        s.add(pet_vars[i] >= 0, pet_vars[i] < 6)
        s.add(phone_vars[i] >= 0, phone_vars[i] < 6)

    # Add distinct constraints
    s.add(Distinct(name_vars))
    s.add(Distinct(food_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(drink_vars))
    s.add(Distinct(pet_vars))
    s.add(Distinct(phone_vars))

    # Map attribute values to indices
    name_idx = {name: idx for idx, name in enumerate(names)}
    food_idx = {food: idx for idx, food in enumerate(foods)}
    height_idx = {height: idx for idx, height in enumerate(heights)}
    drink_idx = {drink: idx for idx, drink in enumerate(drinks)}
    pet_idx = {pet: idx for idx, pet in enumerate(pets)}
    phone_idx = {phone: idx for idx, phone in enumerate(phones)}

    # Add clues as constraints
    # Clue 1: iPhone 13 in third house
    s.add(phone_vars[2] == phone_idx['iphone 13'])

    # Clue 2: Bob is tall
    for i in range(6):
        s.add(Implies(name_vars[i] == name_idx['Bob'], height_vars[i] == height_idx['tall']))

    # Clue 3: Soup in second house
    s.add(food_vars[1] == food_idx['soup'])

    # Clue 4: Root beer left of Xiaomi Mi 11
    for i in range(5):
        s.add(Implies(drink_vars[i] == drink_idx['root beer'], phone_vars[i+1] == phone_idx['xiaomi mi 11']))

    # Clue 5: Huawei P50 left of grilled cheese
    for i in range(5):
        s.add(Implies(phone_vars[i] == phone_idx['huawei p50'], food_vars[i+1] == food_idx['grilled cheese']))

    # Clue 6: Stir fry and milk same person
    for i in range(6):
        s.add(Implies(food_vars[i] == food_idx['stir fry'], drink_vars[i] == drink_idx['milk']))
        s.add(Implies(drink_vars[i] == drink_idx['milk'], food_vars[i] == food_idx['stir fry']))

    # Clue 7: Grilled cheese and tall same person
    for i in range(6):
        s.add(Implies(food_vars[i] == food_idx['grilled cheese'], height_vars[i] == height_idx['tall']))
        s.add(Implies(height_vars[i] == height_idx['tall'], food_vars[i] == food_idx['grilled cheese']))

    # Clue 8: Xiaomi Mi 11 and coffee same person
    for i in range(6):
        s.add(Implies(phone_vars[i] == phone_idx['xiaomi mi 11'], drink_vars[i] == drink_idx['coffee']))
        s.add(Implies(drink_vars[i] == drink_idx['coffee'], phone_vars[i] == phone_idx['xiaomi mi 11']))

    # Clue 9: OnePlus 9 is Arnold
    for i in range(6):
        s.add(Implies(phone_vars[i] == phone_idx['oneplus 9'], name_vars[i] == name_idx['Arnold']))
        s.add(Implies(name_vars[i] == name_idx['Arnold'], phone_vars[i] == phone_idx['oneplus 9']))

    # Clue 10: Rabbit not in fifth house
    s.add(pet_vars[4] != pet_idx['rabbit'])

    # Clue 11: Hamster right of Google Pixel 6
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(pet_vars[i] == pet_idx['hamster'], phone_vars[j] == phone_idx['google pixel 6']), i > j))

    # Clue 12: Super tall and fish same person
    for i in range(6):
        s.add(Implies(height_vars[i] == height_idx['super tall'], pet_vars[i] == pet_idx['fish']))
        s.add(Implies(pet_vars[i] == pet_idx['fish'], height_vars[i] == height_idx['super tall']))

    # Clue 13: Fish is Alice
    for i in range(6):
        s.add(Implies(pet_vars[i] == pet_idx['fish'], name_vars[i] == name_idx['Alice']))
        s.add(Implies(name_vars[i] == name_idx['Alice'], pet_vars[i] == pet_idx['fish']))

    # Clue 14: Tea left of pizza
    for i in range(5):
        s.add(Implies(drink_vars[i] == drink_idx['tea'], food_vars[i+1] == food_idx['pizza']))

    # Clue 15: Samsung Galaxy S21 is Carol
    for i in range(6):
        s.add(Implies(phone_vars[i] == phone_idx['samsung galaxy s21'], name_vars[i] == name_idx['Carol']))
        s.add(Implies(name_vars[i] == name_idx['Carol'], phone_vars[i] == phone_idx['samsung galaxy s21']))

    # Clue 16: Pizza and short same person
    for i in range(6):
        s.add(Implies(food_vars[i] == food_idx['pizza'], height_vars[i] == height_idx['short']))
        s.add(Implies(height_vars[i] == height_idx['short'], food_vars[i] == food_idx['pizza']))

    # Clue 17: Arnold is very tall
    for i in range(6):
        s.add(Implies(name_vars[i] == name_idx['Arnold'], height_vars[i] == height_idx['very tall']))
        s.add(Implies(height_vars[i] == height_idx['very tall'], name_vars[i] == name_idx['Arnold']))

    # Clue 18: Spaghetti and Google Pixel 6 same person
    for i in range(6):
        s.add(Implies(food_vars[i] == food_idx['spaghetti'], phone_vars[i] == phone_idx['google pixel 6']))
        s.add(Implies(phone_vars[i] == phone_idx['google pixel 6'], food_vars[i] == food_idx['spaghetti']))

    # Clue 19: Boba tea right of soup
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(drink_vars[i] == drink_idx['boba tea'], food_vars[j] == food_idx['soup']), i > j))

    # Clue 20: Hamster not in fifth house
    s.add(pet_vars[4] != pet_idx['hamster'])

    # Clue 21: Very tall not in second house
    s.add(height_vars[1] != height_idx['very tall'])

    # Clue 22: Super tall left of Peter
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(height_vars[i] == height_idx['super tall'], name_vars[j] == name_idx['Peter']), i < j))

    # Clue 23: Very short and spaghetti same person
    for i in range(6):
        s.add(Implies(height_vars[i] == height_idx['very short'], food_vars[i] == food_idx['spaghetti']))
        s.add(Implies(food_vars[i] == food_idx['spaghetti'], height_vars[i] == height_idx['very short']))

    # Clue 24: Bird left of spaghetti
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(pet_vars[i] == pet_idx['bird'], food_vars[j] == food_idx['spaghetti']), i < j))

    # Clue 25: Fish left of Eric
    for i in range(5):
        s.add(Implies(pet_vars[i] == pet_idx['fish'], name_vars[i+1] == name_idx['Eric']))

    # Clue 26: Dog and milk same person
    for i in range(6):
        s.add(Implies(pet_vars[i] == pet_idx['dog'], drink_vars[i] == drink_idx['milk']))
        s.add(Implies(drink_vars[i] == drink_idx['milk'], pet_vars[i] == pet_idx['dog']))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(6):
            n = model.evaluate(name_vars[i]).as_long()
            f = model.evaluate(food_vars[i]).as_long()
            h = model.evaluate(height_vars[i]).as_long()
            d = model.evaluate(drink_vars[i]).as_long()
            p = model.evaluate(pet_vars[i]).as_long()
            ph = model.evaluate(phone_vars[i]).as_long()
            rows.append([
                str(i+1),
                names[n],
                foods[f],
                heights[h],
                drinks[d],
                pets[p],
                phones[ph]
            ])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()