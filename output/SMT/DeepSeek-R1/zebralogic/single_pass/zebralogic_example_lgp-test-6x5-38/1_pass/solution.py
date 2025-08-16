from z3 import *
import json

def main():
    # Define the attribute lists
    names = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
    birthdays = ['feb', 'mar', 'sept', 'jan', 'may', 'april']
    foods = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    heights = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
    carmodels = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']

    # Create mappings from attribute value to index
    name_index = {name: idx for idx, name in enumerate(names)}
    bd_index = {bd: idx for idx, bd in enumerate(birthdays)}
    food_index = {food: idx for idx, food in enumerate(foods)}
    height_index = {h: idx for idx, h in enumerate(heights)}
    car_index = {car: idx for idx, car in enumerate(carmodels)}

    # Arrays for each attribute per house (0 to 5)
    n = [Int('n_%d' % i) for i in range(6)]  # names
    b = [Int('b_%d' % i) for i in range(6)]  # birthdays
    f = [Int('f_%d' % i) for i in range(6)]  # foods
    h_arr = [Int('h_%d' % i) for i in range(6)]  # heights
    c = [Int('c_%d' % i) for i in range(6)]  # car models

    s = Solver()

    # Each attribute must be between 0 and 5 and distinct
    for arr in [n, b, f, h_arr, c]:
        s.add([And(arr[i] >= 0, arr[i] < 6) for i in range(6)])
        s.add(Distinct(arr))

    # Clue 1: Honda Civic owner is short
    for i in range(6):
        s.add(Implies(c[i] == car_index['honda civic'], h_arr[i] == height_index['short']))

    # Clue 2: Ford F-150 in fifth house (index 4)
    s.add(c[4] == car_index['ford f150'])

    # Clue 3: Stir fry lover left of Eric
    s.add(Or([And(f[i] == food_index['stir fry'], n[j] == name_index['Eric'], i < j) for i in range(6) for j in range(6) if i < j]))

    # Clue 4: May birthday left of Carol
    s.add(Or([And(b[i] == bd_index['may'], n[j] == name_index['Carol'], i < j) for i in range(6) for j in range(6) if i < j]))

    # Clue 5: Very short (fixed at house 3) left of April birthday
    s.add(Or(b[4] == bd_index['april'], b[5] == bd_index['april']))

    # Clue 6: BMW 3 Series not in third house (index 2)
    s.add(c[2] != car_index['bmw 3 series'])

    # Clue 7: Two houses between stir fry and pizza lovers
    s.add(Or([And(f[i] == food_index['stir fry'], f[j] == food_index['pizza'], Or(i - j == 3, j - i == 3)) for i in range(6) for j in range(6) if i != j]))

    # Clue 8: Soup eater directly left of Eric
    s.add(Or([And(f[i] == food_index['soup'], n[i+1] == name_index['Eric']) for i in range(5)]))

    # Clue 9: Spaghetti eater and May birthday adjacent
    s.add(Or([And(f[i] == food_index['spaghetti'], b[j] == bd_index['may'], Or(i - j == 1, j - i == 1)) for i in range(6) for j in range(6) if i != j]))

    # Clue 10: Alice directly left of BMW 3 Series owner
    s.add(Or([And(n[i] == name_index['Alice'], c[i+1] == car_index['bmw 3 series']) for i in range(5)]))

    # Clue 11: Tesla Model 3 owner left of tall person
    s.add(Or([And(c[i] == car_index['tesla model 3'], h_arr[j] == height_index['tall'], i < j) for i in range(6) for j in range(6) if i < j]))

    # Clue 12: Very tall person owns Toyota Camry
    for i in range(6):
        s.add(Implies(h_arr[i] == height_index['very tall'], c[i] == car_index['toyota camry']))

    # Clue 13: Peter directly left of pizza lover
    s.add(Or([And(n[i] == name_index['Peter'], f[i+1] == food_index['pizza']) for i in range(5)]))

    # Clue 14: Stew not in third house (index 2)
    s.add(f[2] != food_index['stew'])

    # Clue 15: One house between September birthday and very short (fixed at house 3)
    s.add(Or(b[1] == bd_index['sept'], b[5] == bd_index['sept']))

    # Clue 16: One house between March birthday and super tall
    s.add(Or([And(b[i] == bd_index['mar'], h_arr[j] == height_index['super tall'], Or(i - j == 2, j - i == 2)) for i in range(6) for j in range(6)]))

    # Clue 17: Tall person is Bob
    for i in range(6):
        s.add(Implies(h_arr[i] == height_index['tall'], n[i] == name_index['Bob']))

    # Clue 18: May birthday right of Alice
    s.add(Or([And(b[i] == bd_index['may'], n[j] == name_index['Alice'], i > j) for i in range(6) for j in range(6) if i > j]))

    # Clue 19: Very short in fourth house (index 3)
    s.add(h_arr[3] == height_index['very short'])

    # Clue 20: March birthday is short
    for i in range(6):
        s.add(Implies(b[i] == bd_index['mar'], h_arr[i] == height_index['short']))

    # Clue 21: Carol owns Tesla Model 3
    for i in range(6):
        s.add(Implies(n[i] == name_index['Carol'], c[i] == car_index['tesla model 3']))

    # Clue 22: Eric has January birthday
    for i in range(6):
        s.add(Implies(n[i] == name_index['Eric'], b[i] == bd_index['jan']))

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(6):
            name_val = names[m.eval(n[i]).as_long()]
            bd_val = birthdays[m.eval(b[i]).as_long()]
            food_val = foods[m.eval(f[i]).as_long()]
            height_val = heights[m.eval(h_arr[i]).as_long()]
            car_val = carmodels[m.eval(c[i]).as_long()]
            rows.append([str(i+1), name_val, bd_val, food_val, height_val, car_val])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()