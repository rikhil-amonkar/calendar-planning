from z3 import *
import json

def main():
    solver = Solver()

    houses = [1, 2, 3, 4, 5]

    # Variables for each house (1-5, 0-based index in the lists)
    name_vars = [Int(f'name_{h}') for h in houses]
    vacation_vars = [Int(f'vacation_{h}') for h in houses]
    education_vars = [Int(f'education_{h}') for h in houses]
    color_vars = [Int(f'color_{h}') for h in houses]
    phone_vars = [Int(f'phone_{h}') for h in houses]
    food_vars = [Int(f'food_{h}') for h in houses]

    # Constraints for distinct and range
    for vars_list in [name_vars, vacation_vars, education_vars, color_vars, phone_vars, food_vars]:
        for v in vars_list:
            solver.add(And(0 <= v, v <= 4))
        solver.add(Distinct(vars_list))

    # Clue 1: Food_1 != 4 (stew not in first house)
    solver.add(food_vars[0] != 4)

    # Clue 2: two houses between stir fry (food=1) and associate (education=3)
    for h1_idx in range(5):
        for h2_idx in range(5):
            h1 = houses[h1_idx]
            h2 = houses[h2_idx]
            if abs(h1 - h2) != 3:
                solver.add(Not(And(food_vars[h1_idx] == 1, education_vars[h2_idx] == 3)))

    # Clue 3: mountain (0) is bachelor (2)
    for h_idx in range(5):
        solver.add(Implies(vacation_vars[h_idx] == 0, education_vars[h_idx] == 2))

    # Clue 4: doctorate (0) is to the right of Bob (3)
    h_doctorate = Int('h_doctorate')
    h_bob = Int('h_bob')
    solver.add(And(1 <= h_doctorate, h_doctorate <=5))
    solver.add(And(1 <= h_bob, h_bob <=5))
    for h_idx in range(5):
        h_num = houses[h_idx]
        solver.add(Implies(education_vars[h_idx] == 0, h_doctorate == h_num))
        solver.add(Implies(name_vars[h_idx] == 3, h_bob == h_num))
    solver.add(h_doctorate > h_bob)

    # Clue 5: Samsung Galaxy S21 (4) is in house 3
    solver.add(phone_vars[2] == 4)

    # Clue 6: Eric (1) has doctorate (0)
    for h_idx in range(5):
        solver.add(Implies(name_vars[h_idx] == 1, education_vars[h_idx] == 0))

    # Clue 7: doctorate is in third house
    solver.add(education_vars[2] == 0)

    # Clue 8: stir fry (1) is bachelor (2)
    for h_idx in range(5):
        solver.add(Implies(food_vars[h_idx] == 1, education_vars[h_idx] == 2))
        solver.add(Implies(education_vars[h_idx] == 2, food_vars[h_idx] == 1))

    # Clue 9: doctorate (0) is pizza (2)
    for h_idx in range(5):
        solver.add(Implies(education_vars[h_idx] == 0, food_vars[h_idx] == 2))
        solver.add(Implies(food_vars[h_idx] == 2, education_vars[h_idx] == 0))

    # Clue 10: green (4) is to the right of Peter (4)
    h_green = Int('h_green')
    h_peter = Int('h_peter')
    solver.add(And(1 <= h_green, h_green <=5))
    solver.add(And(1 <= h_peter, h_peter <=5))
    for h_idx in range(5):
        h_num = houses[h_idx]
        solver.add(Implies(color_vars[h_idx] ==4, h_green == h_num))
        solver.add(Implies(name_vars[h_idx] ==4, h_peter == h_num))
    solver.add(h_green > h_peter)

    # Clue 11: camping (4) is iPhone 13 (1)
    for h_idx in range(5):
        solver.add(Implies(vacation_vars[h_idx] ==4, phone_vars[h_idx] ==1))
        solver.add(Implies(phone_vars[h_idx] ==1, vacation_vars[h_idx] ==4))

    # Clue 12: cruise (2) is Alice (2)
    for h_idx in range(5):
        solver.add(Implies(vacation_vars[h_idx] ==2, name_vars[h_idx] ==2))
        solver.add(Implies(name_vars[h_idx] ==2, vacation_vars[h_idx] ==2))

    # Clue 13: high school (1) is two away from Samsung Galaxy S21 (3)
    solver.add(Or(education_vars[0] ==1, education_vars[4] ==1))  # house 1 or 5

    # Clue 14: Google Pixel 6 (0) is Arnold (0)
    for h_idx in range(5):
        solver.add(Implies(phone_vars[h_idx] ==0, name_vars[h_idx] ==0))
        solver.add(Implies(name_vars[h_idx] ==0, phone_vars[h_idx] ==0))

    # Clue 15: OnePlus 9 (2) is to the right of Huawei P50 (3)
    h_oneplus = Int('h_oneplus')
    h_huawei = Int('h_huawei')
    solver.add(And(1 <= h_oneplus, h_oneplus <=5))
    solver.add(And(1 <= h_huawei, h_huawei <=5))
    for h_idx in range(5):
        h_num = houses[h_idx]
        solver.add(Implies(phone_vars[h_idx] ==2, h_oneplus == h_num))
        solver.add(Implies(phone_vars[h_idx] ==3, h_huawei == h_num))
    solver.add(h_oneplus > h_huawei)

    # Clue 16: Arnold (0) loves grilled cheese (0)
    for h_idx in range(5):
        solver.add(Implies(name_vars[h_idx] ==0, food_vars[h_idx] ==0))
        solver.add(Implies(food_vars[h_idx] ==0, name_vars[h_idx] ==0))

    # Clue 17: grilled cheese (0) not in fourth house
    solver.add(food_vars[3] != 0)

    # Clue 18: bachelor (2) and red (1) differ by 3
    for h1_idx in range(5):
        for h2_idx in range(5):
            h1 = houses[h1_idx]
            h2 = houses[h2_idx]
            if abs(h1 - h2) !=3:
                solver.add(Not(And(education_vars[h1_idx] ==2, color_vars[h2_idx] ==1)))

    # Clue 19: beach (3) is to the right of city (1)
    h_city = Int('h_city')
    h_beach = Int('h_beach')
    solver.add(And(1 <= h_city, h_city <=5))
    solver.add(And(1 <= h_beach, h_beach <=5))
    for h_idx in range(5):
        h_num = houses[h_idx]
        solver.add(Implies(vacation_vars[h_idx] ==1, h_city == h_num))
        solver.add(Implies(vacation_vars[h_idx] ==3, h_beach == h_num))
    solver.add(h_beach > h_city)

    # Clue 20: green (4) not in second house
    solver.add(color_vars[1] !=4)

    # Clue 21: blue (0) is to the right of Peter (4)
    h_blue = Int('h_blue')
    h_peter_name = Int('h_peter_name')
    solver.add(And(1 <= h_blue, h_blue <=5))
    solver.add(And(1 <= h_peter_name, h_peter_name <=5))
    for h_idx in range(5):
        h_num = houses[h_idx]
        solver.add(Implies(color_vars[h_idx] ==0, h_blue == h_num))
        solver.add(Implies(name_vars[h_idx] ==4, h_peter_name == h_num))
    solver.add(h_blue > h_peter_name)

    # Clue 22: camping (4) and yellow (3) differ by 2
    for h1_idx in range(5):
        for h2_idx in range(5):
            h1 = houses[h1_idx]
            h2 = houses[h2_idx]
            if abs(h1 - h2) !=2:
                solver.add(Not(And(vacation_vars[h1_idx] ==4, color_vars[h2_idx] ==3)))

    # Check if the solver is satisfiable
    if solver.check() == sat:
        model = solver.model()

        # Mapping functions
        name_map = {0: 'Arnold', 1: 'Eric', 2: 'Alice', 3: 'Bob', 4: 'Peter'}
        vacation_map = {0: 'mountain', 1: 'city', 2: 'cruise', 3: 'beach', 4: 'camping'}
        education_map = {0: 'doctorate', 1: 'high school', 2: 'bachelor', 3: 'associate', 4: 'master'}
        color_map = {0: 'blue', 1: 'red', 2: 'white', 3: 'yellow', 4: 'green'}
        phone_map = {0: 'google pixel 6', 1: 'iphone 13', 2: 'oneplus 9', 3: 'huawei p50', 4: 'samsung galaxy s21'}
        food_map = {0: 'grilled cheese', 1: 'stir fry', 2: 'pizza', 3: 'spaghetti', 4: 'stew'}

        # Prepare the solution rows
        rows = []
        for h_idx in range(5):
            house_num = houses[h_idx]
            name_val = name_map[model[name_vars[h_idx]].as_long()]
            vacation_val = vacation_map[model[vacation_vars[h_idx]].as_long()]
            education_val = education_map[model[education_vars[h_idx]].as_long()]
            color_val = color_map[model[color_vars[h_idx]].as_long()]
            phone_val = phone_map[model[phone_vars[h_idx]].as_long()]
            food_val = food_map[model[food_vars[h_idx]].as_long()]
            rows.append([str(house_num), name_val, vacation_val, education_val, color_val, phone_val, food_val])

        # Prepare the JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()