from z3 import *
import json

# Define EnumSorts for each attribute
Names, (Eric, Peter, Arnold, Alice, Bob) = EnumSort('Names', ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob'])
Foods, (stir_fry, spaghetti, stew, grilled_cheese, pizza) = EnumSort('Foods', ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza'])
CarModels, (ford_f150, tesla_model_3, bmw_3_series, toyota_camry, honda_civic) = EnumSort('CarModels', ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic'])
PhoneModels, (iphone_13, google_pixel_6, samsung_galaxy_s21, oneplus_9, huawei_p50) = EnumSort('PhoneModels', ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50'])
Occupations, (teacher, lawyer, doctor, artist, engineer) = EnumSort('Occupations', ['teacher', 'lawyer', 'doctor', 'artist', 'engineer'])
Drinks, (tea, milk, water, root_beer, coffee) = EnumSort('Drinks', ['tea', 'milk', 'water', 'root beer', 'coffee'])

# Create variables for each house (0-4 for houses 1-5)
names = [Const(f"name_{i}", Names) for i in range(5)]
foods = [Const(f"food_{i}", Foods) for i in range(5)]
cars = [Const(f"car_{i}", CarModels) for i in range(5)]
phones = [Const(f"phone_{i}", PhoneModels) for i in range(5)]
occupations = [Const(f"occupation_{i}", Occupations) for i in range(5)]
drinks = [Const(f"drink_{i}", Drinks) for i in range(5)]

solver = Solver()

# Add distinct constraints for each attribute
solver.add(Distinct(names))
solver.add(Distinct(foods))
solver.add(Distinct(cars))
solver.add(Distinct(phones))
solver.add(Distinct(occupations))
solver.add(Distinct(drinks))

# Add all the clues as constraints
# Clue 1: Root beer lover owns Honda Civic
solver.add(Or([And(drinks[h] == root_beer, cars[h] == honda_civic) for h in range(5)]))

# Clue 2: Milk drinker is directly left of grilled cheese eater
solver.add(Or([And(drinks[h] == milk, foods[h+1] == grilled_cheese) for h in range(4)]))

# Clue 3: Alice uses Samsung Galaxy S21
solver.add(Or([And(names[h] == Alice, phones[h] == samsung_galaxy_s21) for h in range(5)]))

# Clue 4: Alice loves stir fry
solver.add(Or([And(names[h] == Alice, foods[h] == stir_fry) for h in range(5)]))

# Clue 5: Tea drinker is not in the fifth house
solver.add(drinks[4] != tea)

# Clue 6: BMW 3 Series owner is left of tea drinker
solver.add(Or([And(cars[i] == bmw_3_series, drinks[j] == tea, i < j) for i in range(5) for j in range(5)]))

# Clue 7: Arnold is the doctor
solver.add(Or([And(names[h] == Arnold, occupations[h] == doctor) for h in range(5)]))

# Clue 8: iPhone 13 user is coffee drinker
solver.add(Or([And(phones[h] == iphone_13, drinks[h] == coffee) for h in range(5)]))

# Clue 9: Engineer owns BMW 3 Series
solver.add(Or([And(occupations[h] == engineer, cars[h] == bmw_3_series) for h in range(5)]))

# Clue 10: Stew lover uses iPhone 13
solver.add(Or([And(foods[h] == stew, phones[h] == iphone_13) for h in range(5)]))

# Clue 11: Doctor is directly left of OnePlus 9 user
solver.add(Or([And(occupations[h] == doctor, phones[h+1] == oneplus_9) for h in range(4)]))

# Clue 12: Honda Civic is directly left of spaghetti eater
solver.add(Or([And(cars[h] == honda_civic, foods[h+1] == spaghetti) for h in range(4)]))

# Clue 13: Google Pixel 6 user is tea drinker
solver.add(Or([And(phones[h] == google_pixel_6, drinks[h] == tea) for h in range(5)]))

# Clue 14: Alice is an artist
solver.add(Or([And(names[h] == Alice, occupations[h] == artist) for h in range(5)]))

# Clue 15: One house between Alice and Ford F-150 owner
solver.add(Or([And(names[i] == Alice, cars[j] == ford_f150, Or(i - j == 2, j - i == 2)) for i in range(5) for j in range(5)]))

# Clue 16: Arnold owns Toyota Camry
solver.add(Or([And(names[h] == Arnold, cars[h] == toyota_camry) for h in range(5)]))

# Clue 17: Eric is in the fourth house
solver.add(names[3] == Eric)

# Clue 18: OnePlus 9 user is a lawyer
solver.add(Or([And(phones[h] == oneplus_9, occupations[h] == lawyer) for h in range(5)]))

# Clue 19: Peter is the grilled cheese lover
solver.add(Or([And(names[h] == Peter, foods[h] == grilled_cheese) for h in range(5)]))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    solution_rows = []
    for h in range(5):
        house_num = h + 1
        name = str(model.eval(names[h]))
        food = str(model.eval(foods[h]))
        car = str(model.eval(cars[h]))
        phone = str(model.eval(phones[h]))
        occupation = str(model.eval(occupations[h]))
        drink = str(model.eval(drinks[h]))
        solution_rows.append([str(house_num), name, food, car, phone, occupation, drink])
    json_output = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": solution_rows
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")