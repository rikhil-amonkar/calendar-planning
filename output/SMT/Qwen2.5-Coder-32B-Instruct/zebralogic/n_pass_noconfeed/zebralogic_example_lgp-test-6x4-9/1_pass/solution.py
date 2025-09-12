from z3 import *

def solve_puzzle():
    # Define domains
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    phones = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    colors = ["blue", "red", "yellow", "green", "white", "purple"]

    # Create variables
    house_vars = {name: Int(f"house_{name}") for name in names}
    phone_vars = {name: String(f"phone_{name}") for name in names}
    nationality_vars = {name: String(f"nationality_{name}") for name in names}
    color_vars = {name: String(f"color_{name}") for name in names}

    # Create solver
    solver = Solver()

    # Add domain constraints
    for name in names:
        solver.add(house_vars[name] >= 1)
        solver.add(house_vars[name] <= 6)
        solver.add(phone_vars[name] == Or([String(phone) for phone in phones]))
        solver.add(nationality_vars[name] == Or([String(nationality) for nationality in nationalities]))
        solver.add(color_vars[name] == Or([String(color) for color in colors]))

    # All values must be unique
    solver.add(Distinct([house_vars[name] for name in names]))
    solver.add(Distinct([phone_vars[name] for name in names]))
    solver.add(Distinct([nationality_vars[name] for name in names]))
    solver.add(Distinct([color_vars[name] for name in names]))

    # Clues
    solver.add(house_vars["Carol"] != 3)
    solver.add(Abs(house_vars["Dane"] - house_vars["brit"]) == 2)
    solver.add(color_vars["Carol"] == "green")
    solver.add(house_vars["Arnold"] + 1 == house_vars["Alice"])
    solver.add(nationality_vars["Alice"] == "german")
    solver.add(phone_vars[String("OnePlus 9")] == "purple")
    solver.add(phone_vars[String("Huawei P50")] != 3)
    solver.add(phone_vars[String("Samsung Galaxy S21")] == 5)
    solver.add(Or([And(house_vars[name1] < house_vars[name2], color_vars[name1] == "red", color_vars[name2] == "white") for name1 in names for name2 in names if name1 != name2]))
    solver.add(phone_vars[String("Samsung Galaxy S21")] == house_vars["Bob"])
    solver.add(nationality_vars["Dane"] == "yellow")
    solver.add(house_vars["Bob"] < house_vars["Peter"])
    solver.add(color_vars["Peter"] == "blue")
    solver.add(nationality_vars["Peter"] == "brit")
    solver.add(house_vars["Bob"] + 1 == house_vars[phone_vars[String("iPhone 13")]])
    solver.add(nationality_vars[String("Norwegian")] == "purple")
    solver.add(nationality_vars[String("Chinese")] == "xiaomi mi 11")

    # Solve
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            for name in names:
                if model.evaluate(house_vars[name]) == house:
                    phone = model.evaluate(phone_vars[name]).as_string()[1:-1]
                    nationality = model.evaluate(nationality_vars[name]).as_string()[1:-1]
                    color = model.evaluate(color_vars[name]).as_string()[1:-1]
                    solution.append([str(house), name, phone, nationality, color])
        return solution
    else:
        return None

# Generate JSON output
import json

solution_data = solve_puzzle()
output_json = {
    "solution": {
        "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
        "rows": solution_data
    }
}

print(json.dumps(output_json, indent=2))