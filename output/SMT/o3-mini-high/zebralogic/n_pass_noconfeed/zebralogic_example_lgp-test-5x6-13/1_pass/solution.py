from z3 import *
import json

def main():
    solver = Solver()
    houses = 5
    # Create integer variables for each house and attribute.
    names = [Int("name_%d" % i) for i in range(houses)]
    foods = [Int("food_%d" % i) for i in range(houses)]
    cars = [Int("car_%d" % i) for i in range(houses)]
    phones = [Int("phone_%d" % i) for i in range(houses)]
    occs = [Int("occ_%d" % i) for i in range(houses)]
    drinks = [Int("drink_%d" % i) for i in range(houses)]
    
    # Domain constraints: each variable takes a value between 0 and 4.
    for i in range(houses):
        solver.add(And(names[i] >= 0, names[i] < 5))
        solver.add(And(foods[i] >= 0, foods[i] < 5))
        solver.add(And(cars[i] >= 0, cars[i] < 5))
        solver.add(And(phones[i] >= 0, phones[i] < 5))
        solver.add(And(occs[i] >= 0, occs[i] < 5))
        solver.add(And(drinks[i] >= 0, drinks[i] < 5))
    
    # All-different constraints for each attribute category.
    solver.add(Distinct(names))
    solver.add(Distinct(foods))
    solver.add(Distinct(cars))
    solver.add(Distinct(phones))
    solver.add(Distinct(occs))
    solver.add(Distinct(drinks))
    
    # Mapping of values:
    # Names: 0:"Eric", 1:"Peter", 2:"Arnold", 3:"Alice", 4:"Bob"
    # Foods: 0:"stir fry", 1:"spaghetti", 2:"stew", 3:"grilled cheese", 4:"pizza"
    # Cars: 0:"ford f150", 1:"tesla model 3", 2:"bmw 3 series", 3:"toyota camry", 4:"honda civic"
    # Phones: 0:"iphone 13", 1:"google pixel 6", 2:"samsung galaxy s21", 3:"oneplus 9", 4:"huawei p50"
    # Occupations: 0:"teacher", 1:"lawyer", 2:"doctor", 3:"artist", 4:"engineer"
    # Drinks: 0:"tea", 1:"milk", 2:"water", 3:"root beer", 4:"coffee"
    
    # Clue 1: The root beer lover (drink == 3) is the person who owns a Honda Civic (car == 4).
    for i in range(houses):
        solver.add(Implies(drinks[i] == 3, cars[i] == 4))
        solver.add(Implies(cars[i] == 4, drinks[i] == 3))
    
    # Clue 2: The person who likes milk (drink == 1) is directly left of the person who loves grilled cheese (food == 3).
    for i in range(houses - 1):
        solver.add(Implies(drinks[i] == 1, foods[i+1] == 3))
    for i in range(1, houses):
        solver.add(Implies(foods[i] == 3, drinks[i-1] == 1))
    
    # Clue 3: Alice (name == 3) uses a Samsung Galaxy S21 (phone == 2).
    for i in range(houses):
        solver.add(Implies(names[i] == 3, phones[i] == 2))
    
    # Clue 4: Alice (name == 3) loves stir fry (food == 0).
    for i in range(houses):
        solver.add(Implies(names[i] == 3, foods[i] == 0))
    
    # Clue 5: The tea drinker (drink == 0) is not in the fifth house (index 4).
    solver.add(drinks[4] != 0)
    
    # Clue 6: The person who owns a BMW 3 Series (car == 2) is somewhere to the left of the tea drinker (drink == 0).
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(cars[i] == 2, drinks[j] == 0), i < j))
    
    # Clue 7: The person who is a doctor (occ == 2) is Arnold (name == 2).
    for i in range(houses):
        solver.add(Implies(names[i] == 2, occs[i] == 2))
        solver.add(Implies(occs[i] == 2, names[i] == 2))
    
    # Clue 8: The person who uses an iPhone 13 (phone == 0) is the coffee drinker (drink == 4).
    for i in range(houses):
        solver.add(Implies(phones[i] == 0, drinks[i] == 4))
        solver.add(Implies(drinks[i] == 4, phones[i] == 0))
    
    # Clue 9: The person who is an engineer (occ == 4) owns a BMW 3 Series (car == 2).
    for i in range(houses):
        solver.add(Implies(occs[i] == 4, cars[i] == 2))
        solver.add(Implies(cars[i] == 2, occs[i] == 4))
    
    # Clue 10: The person who loves stew (food == 2) uses an iPhone 13 (phone == 0).
    for i in range(houses):
        solver.add(Implies(foods[i] == 2, phones[i] == 0))
        solver.add(Implies(phones[i] == 0, foods[i] == 2))
    
    # Clue 11: The doctor (occ == 2) is directly left of the person who uses a OnePlus 9 (phone == 3).
    for i in range(houses - 1):
        solver.add(Implies(occs[i] == 2, phones[i+1] == 3))
    for i in range(1, houses):
        solver.add(Implies(phones[i] == 3, occs[i-1] == 2))
    
    # Clue 12: The person who owns a Honda Civic (car == 4) is directly left of the person who loves spaghetti (food == 1).
    for i in range(houses - 1):
        solver.add(Implies(cars[i] == 4, foods[i+1] == 1))
    for i in range(1, houses):
        solver.add(Implies(foods[i] == 1, cars[i-1] == 4))
    
    # Clue 13: The person who uses a Google Pixel 6 (phone == 1) is the tea drinker (drink == 0).
    for i in range(houses):
        solver.add(Implies(phones[i] == 1, drinks[i] == 0))
        solver.add(Implies(drinks[i] == 0, phones[i] == 1))
    
    # Clue 14: Alice (name == 3) is the artist (occ == 3).
    for i in range(houses):
        solver.add(Implies(names[i] == 3, occs[i] == 3))
        solver.add(Implies(occs[i] == 3, names[i] == 3))
    
    # Clue 15: There is one house between Alice (name == 3) and the person who owns a Ford F-150 (car == 0).
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(names[i] == 3, cars[j] == 0), Abs(i - j) == 2))
    
    # Clue 16: Arnold (name == 2) owns a Toyota Camry (car == 3).
    for i in range(houses):
        solver.add(Implies(names[i] == 2, cars[i] == 3))
        solver.add(Implies(cars[i] == 3, names[i] == 2))
    
    # Clue 17: Eric (name == 0) is in the fourth house (index 3).
    solver.add(names[3] == 0)
    
    # Clue 18: The person who uses a OnePlus 9 (phone == 3) is the lawyer (occ == 1).
    for i in range(houses):
        solver.add(Implies(phones[i] == 3, occs[i] == 1))
        solver.add(Implies(occs[i] == 1, phones[i] == 3))
    
    # Clue 19: The person who loves grilled cheese (food == 3) is Peter (name == 1).
    for i in range(houses):
        solver.add(Implies(foods[i] == 3, names[i] == 1))
        solver.add(Implies(names[i] == 1, foods[i] == 3))
    
    if solver.check() == sat:
        model = solver.model()
        # Define the mappings to convert numeric values to their corresponding strings.
        nameMap = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
        foodMap = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
        carMap = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
        phoneMap = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
        occMap = ["teacher", "lawyer", "doctor", "artist", "engineer"]
        drinkMap = ["tea", "milk", "water", "root beer", "coffee"]
        
        rows = []
        for i in range(houses):
            row = [
                str(i + 1),
                nameMap[model.eval(names[i]).as_long()],
                foodMap[model.eval(foods[i]).as_long()],
                carMap[model.eval(cars[i]).as_long()],
                phoneMap[model.eval(phones[i]).as_long()],
                occMap[model.eval(occs[i]).as_long()],
                drinkMap[model.eval(drinks[i]).as_long()]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()