from z3 import *

# Define the variables
names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
house_styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
birthdays = ["mar", "sept", "may", "feb", "jan", "april"]

houses = range(1, 7)

name_vars = {house: Int(f'name_{house}') for house in houses}
pet_vars = {house: Int(f'pet_{house}') for house in houses}
house_style_vars = {house: Int(f'house_style_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}

# Create the solver
solver = Solver()

# Add constraints for unique values in each category
for category_vars in [name_vars, pet_vars, house_style_vars, birthday_vars]:
    for i in houses:
        solver.add(category_vars[i] >= 0)
        solver.add(category_vars[i] < len(names))
    solver.add(Distinct(*category_vars.values()))

# Add specific clues as constraints
# Clue 1
solver.add(name_vars[hamster_house] > name_vars[march_birthday_house] for hamster_house in houses for march_birthday_house in houses if hamster_house != march_birthday_house)

# Clue 2
solver.add(name_vars[january_birthday_house] < name_vars[september_birthday_house] for january_birthday_house in houses for september_birthday_house in houses if january_birthday_house != september_birthday_house)

# Clue 3
solver.add(birthday_vars[2] == birthdays.index("may"))

# Clue 4
solver.add(house_style_vars[2] == house_styles.index("colonial"))

# Clue 5
solver.add(name_vars[3] == names.index("Carol"))

# Clue 6
solver.add(house_style_vars[6] != house_styles.index("mediterranean"))

# Clue 7
solver.add(name_vars[fish_house] > name_vars[bob_house] for fish_house in houses for bob_house in houses if fish_house != bob_house)

# Clue 8
solver.add(name_vars[6] == names.index("Eric"))

# Clue 9
solver.add(Abs(name_vars[cat_house] - name_vars[victorian_house]) == 1 for cat_house in houses for victorian_house in houses if cat_house != victorian_house)

# Clue 10
solver.add(Abs(name_vars[victorian_house] - name_vars[hamster_house]) == 2 for victorian_house in houses for hamster_house in houses if victorian_house != hamster_house)

# Clue 11
solver.add(name_vars[craftsman_house] == names.index("Arnold") for craftsman_house in houses)

# Clue 12
solver.add(house_style_vars[colonial_house] < house_style_vars[modern_house] for colonial_house in houses for modern_house in houses if colonial_house != modern_house)

# Clue 13
solver.add(fish_house != 2 for fish_house in houses)

# Clue 14
solver.add(house_style_vars[peter_house] == house_styles.index("colonial") for peter_house in houses)

# Clue 15
solver.add(name_vars[january_birthday_house] + 1 == name_vars[april_birthday_house] for january_birthday_house in houses for april_birthday_house in houses if january_birthday_house != april_birthday_house)

# Clue 16
solver.add(Abs(name_vars[bird_house] - name_vars[modern_house]) == 1 for bird_house in houses for modern_house in houses if bird_house != modern_house)

# Clue 17
solver.add(birthday_vars[carol_house] == birthdays.index("mar") for carol_house in houses)

# Clue 18
solver.add(house_style_vars[4] == house_styles.index("craftsman"))

# Clue 19
solver.add(pet_vars[4] == pets.index("dog"))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        pet = pets[model.evaluate(pet_vars[house]).as_long()]
        house_style = house_styles[model.evaluate(house_style_vars[house]).as_long()]
        birthday = birthdays[model.evaluate(birthday_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, pet, house_style, birthday])
    
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")