from z3 import *

# Define the solver
solver = Solver()

# Define variables for each attribute
names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
car_models = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
phone_models = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']

# Create arrays for each attribute
house_names = [String('name_%d' % i) for i in range(5)]
house_foods = [String('food_%d' % i) for i in range(5)]
house_car_models = [String('car_model_%d' % i) for i in range(5)]
house_phone_models = [String('phone_model_%d' % i) for i in range(5)]
house_occupations = [String('occupation_%d' % i) for i in range(5)]
house_drinks = [String('drink_%d' % i) for i in range(5)]

# Add constraints for each attribute to be unique
solver.add(Distinct(house_names))
solver.add(Distinct(house_foods))
solver.add(Distinct(house_car_models))
solver.add(Distinct(house_phone_models))
solver.add(Distinct(house_occupations))
solver.add(Distinct(house_drinks))

# Add clues as constraints
# 1. The root beer lover is the person who owns a Honda Civic.
solver.add(Implies(house_drinks[0] == 'root beer', house_car_models[0] == 'honda civic'))
solver.add(Implies(house_drinks[1] == 'root beer', house_car_models[1] == 'honda civic'))
solver.add(Implies(house_drinks[2] == 'root beer', house_car_models[2] == 'honda civic'))
solver.add(Implies(house_drinks[3] == 'root beer', house_car_models[3] == 'honda civic'))
solver.add(Implies(house_drinks[4] == 'root beer', house_car_models[4] == 'honda civic'))

# 2. The person who likes milk is directly left of the person who loves eating grilled cheese.
solver.add(Or(
    And(house_drinks[0] == 'milk', house_foods[1] == 'grilled cheese'),
    And(house_drinks[1] == 'milk', house_foods[2] == 'grilled cheese'),
    And(house_drinks[2] == 'milk', house_foods[3] == 'grilled cheese'),
    And(house_drinks[3] == 'milk', house_foods[4] == 'grilled cheese')
))

# 3. Alice is the person who uses a Samsung Galaxy S21.
solver.add(house_phone_models[i] == 'samsung galaxy s21' for i, name in enumerate(names) if name == 'Alice')

# 4. Alice is the person who loves stir fry.
solver.add(house_foods[i] == 'stir fry' for i, name in enumerate(names) if name == 'Alice')

# 5. The tea drinker is not in the fifth house.
solver.add(house_drinks[4] != 'tea')

# 6. The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
solver.add(Or(
    And(house_car_models[0] == 'bmw 3 series', Or(house_drinks[1] == 'tea', house_drinks[2] == 'tea', house_drinks[3] == 'tea', house_drinks[4] == 'tea')),
    And(house_car_models[1] == 'bmw 3 series', Or(house_drinks[2] == 'tea', house_drinks[3] == 'tea', house_drinks[4] == 'tea')),
    And(house_car_models[2] == 'bmw 3 series', Or(house_drinks[3] == 'tea', house_drinks[4] == 'tea')),
    And(house_car_models[3] == 'bmw 3 series', house_drinks[4] == 'tea')
))

# 7. The person who is a doctor is Arnold.
solver.add(house_occupations[i] == 'doctor' for i, name in enumerate(names) if name == 'Arnold')

# 8. The person who uses an iPhone 13 is the coffee drinker.
solver.add(house_phone_models[i] == 'iphone 13' for i, drink in enumerate(drinks) if drink == 'coffee')

# 9. The person who is an engineer is the person who owns a BMW 3 Series.
solver.add(house_occupations[i] == 'engineer' for i, car_model in enumerate(car_models) if car_model == 'bmw 3 series')

# 10. The person who loves the stew is the person who uses an iPhone 13.
solver.add(house_foods[i] == 'stew' for i, phone_model in enumerate(phone_models) if phone_model == 'iphone 13')

# 11. The person who is a doctor is directly left of the person who uses a OnePlus 9.
solver.add(Or(
    And(house_occupations[0] == 'doctor', house_phone_models[1] == 'oneplus 9'),
    And(house_occupations[1] == 'doctor', house_phone_models[2] == 'oneplus 9'),
    And(house_occupations[2] == 'doctor', house_phone_models[3] == 'oneplus 9'),
    And(house_occupations[3] == 'doctor', house_phone_models[4] == 'oneplus 9')
))

# 12. The person who owns a Honda Civic is directly left of the person who loves the spaghetti eater.
solver.add(Or(
    And(house_car_models[0] == 'honda civic', house_foods[1] == 'spaghetti'),
    And(house_car_models[1] == 'honda civic', house_foods[2] == 'spaghetti'),
    And(house_car_models[2] == 'honda civic', house_foods[3] == 'spaghetti'),
    And(house_car_models[3] == 'honda civic', house_foods[4] == 'spaghetti')
))

# 13. The person who uses a Google Pixel 6 is the tea drinker.
solver.add(house_phone_models[i] == 'google pixel 6' for i, drink in enumerate(drinks) if drink == 'tea')

# 14. Alice is the person who is an artist.
solver.add(house_occupations[i] == 'artist' for i, name in enumerate(names) if name == 'Alice')

# 15. There is one house between Alice and the person who owns a Ford F-150.
for i, name in enumerate(names):
    if name == 'Alice':
        alice_index = i
solver.add(Or(
    And(alice_index == 0, house_car_models[2] == 'ford f150'),
    And(alice_index == 1, house_car_models[3] == 'ford f150'),
    And(alice_index == 2, Or(house_car_models[0] == 'ford f150', house_car_models[4] == 'ford f150')),
    And(alice_index == 3, house_car_models[1] == 'ford f150'),
    And(alice_index == 4, house_car_models[2] == 'ford f150')
))

# 16. Arnold is the person who owns a Toyota Camry.
solver.add(house_car_models[i] == 'toyota camry' for i, name in enumerate(names) if name == 'Arnold')

# 17. Eric is in the fourth house.
solver.add(house_names[3] == 'Eric')

# 18. The person who uses a OnePlus 9 is the person who is a lawyer.
solver.add(house_phone_models[i] == 'oneplus 9' for i, occupation in enumerate(occupations) if occupation == 'lawyer')

# 19. The person who loves eating grilled cheese is Peter.
solver.add(house_foods[i] == 'grilled cheese' for i, name in enumerate(names) if name == 'Peter')

# Check if the solution exists
if solver.check() == sat:
    m = solver.model()
    result = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": []
        }
    }
    for i in range(5):
        result["solution"]["rows"].append([
            str(i + 1),
            m[house_names[i]].as_string(),
            m[house_foods[i]].as_string(),
            m[house_car_models[i]].as_string(),
            m[house_phone_models[i]].as_string(),
            m[house_occupations[i]].as_string(),
            m[house_drinks[i]].as_string()
        ])
    print(json.dumps(result, indent=2))
else:
    print("No solution found")