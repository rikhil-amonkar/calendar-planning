import json
from z3 import *

def solve_puzzle():
    # Initialize the solver
    solver = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the attributes
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phone_models = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']

    # Create variables for each attribute in each house
    name = {h: Const(f'name_{h}', StringSort()) for h in houses}
    phone = {h: Const(f'phone_{h}', StringSort()) for h in houses}
    nationality = {h: Const(f'nationality_{h}', StringSort()) for h in houses}
    color = {h: Const(f'color_{h}', StringSort()) for h in houses}

    # Add constraints that each attribute in each house must be one of the allowed values
    for h in houses:
        solver.add(Or([name[h] == StringVal(n) for n in names]))
        solver.add(Or([phone[h] == StringVal(p) for p in phone_models]))
        solver.add(Or([nationality[h] == StringVal(n) for n in nationalities]))
        solver.add(Or([color[h] == StringVal(c) for c in colors]))

    # Add uniqueness constraints for each attribute across houses
    for attr in [name, phone, nationality, color]:
        for h1 in houses:
            for h2 in houses:
                if h1 < h2:
                    solver.add(attr[h1] != attr[h2])

    # Add clues as constraints
    # 1. Carol is not in the third house.
    solver.add(name[3] != StringVal('Carol'))

    # 2. There is one house between the Dane and the British person.
    for h in houses:
        if h + 2 <= 6:
            solver.add(Or(
                And(nationality[h] == StringVal('dane'), nationality[h + 2] == StringVal('brit')),
                And(nationality[h] == StringVal('brit'), nationality[h + 2] == StringVal('dane'))
            ))

    # 3. Carol is the person whose favorite color is green.
    for h in houses:
        solver.add(Implies(name[h] == StringVal('Carol'), color[h] == StringVal('green')))

    # 4. Arnold is directly left of Alice.
    for h in houses:
        if h < 6:
            solver.add(Implies(name[h] == StringVal('Arnold'), name[h + 1] == StringVal('Alice')))
        else:
            solver.add(name[h] != StringVal('Arnold'))  # Arnold cannot be in the last house

    # 5. Alice is the German.
    for h in houses:
        solver.add(Implies(name[h] == StringVal('Alice'), nationality[h] == StringVal('german'))))

    # 6. The person who uses a OnePlus 9 is the person who loves purple.
    for h in houses:
        solver.add(Implies(phone[h] == StringVal('oneplus 9'), color[h] == StringVal('purple')))

    # 7. The person who uses a Huawei P50 is not in the third house.
    solver.add(phone[3] != StringVal('huawei p50'))

    # 8. The person who uses a Samsung Galaxy S21 is in the fifth house.
    solver.add(phone[5] == StringVal('samsung galaxy s21'))

    # 9. The person who loves white is somewhere to the right of the person whose favorite color is red.
    for h_red in houses:
        for h_white in houses:
            if h_white > h_red:
                solver.add(Implies(
                    And(color[h_red] == StringVal('red'), color[h_white] == StringVal('white')),
                    h_white > h_red
                ))

    # 10. The person who uses a Samsung Galaxy S21 is Bob.
    for h in houses:
        solver.add(Implies(phone[h] == StringVal('samsung galaxy s21'), name[h] == StringVal('Bob')))

    # 11. The Dane is the person who loves yellow.
    for h in houses:
        solver.add(Implies(nationality[h] == StringVal('dane'), color[h] == StringVal('yellow'))))

    # 12. The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    # Since Samsung is in house 5, Peter must be to the right (house 6)
    solver.add(name[6] == StringVal('Peter'))

    # 13. The person who loves blue is Peter.
    for h in houses:
        solver.add(Implies(name[h] == StringVal('Peter'), color[h] == StringVal('blue'))))

    # 14. Peter is the British person.
    for h in houses:
        solver.add(Implies(name[h] == StringVal('Peter'), nationality[h] == StringVal('brit'))))

    # 15. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    solver.add(phone[6] == StringVal('iphone 13'))

    # 16. The Norwegian is the person who loves purple.
    for h in houses:
        solver.add(Implies(nationality[h] == StringVal('norwegian'), color[h] == StringVal('purple'))))

    # 17. The person who uses a Xiaomi Mi 11 is the Chinese.
    for h in houses:
        solver.add(Implies(phone[h] == StringVal('xiaomi mi 11'), nationality[h] == StringVal('chinese'))))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                "rows": []
            }
        }

        for h in houses:
            row = [
                str(h),
                str(model.eval(name[h])),
                str(model.eval(phone[h])),
                str(model.eval(nationality[h])),
                str(model.eval(color[h]))
            ]
            solution["solution"]["rows"].append(row)

        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

# Print the solution
print(solve_puzzle())