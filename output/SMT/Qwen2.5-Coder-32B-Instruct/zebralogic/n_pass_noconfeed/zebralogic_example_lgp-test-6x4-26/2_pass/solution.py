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
# Clue 1: The person with the hamster lives in a house with a higher number than the person born in March.
solver.add(Or([And(pet_vars[h1] == pets.index("hamster"), birthday_vars[h2] == birthdays.index("mar"), h1 > h2) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 2: The person born in January lives in a house with a lower number than the person born in September.
solver.add(Or([And(birthday_vars[h1] == birthdays.index("jan"), birthday_vars[h2] == birthdays.index("sept"), h1 < h2) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 3: The owner of the house numbered 2 was born in May.
solver.add(birthday_vars[2] == birthdays.index("may"))

# Clue 4: The owner of the house numbered 2 lives in a colonial house.
solver.add(house_style_vars[2] == house_styles.index("colonial"))

# Clue 5: Carol lives in house number 3.
solver.add(name_vars[3] == names.index("Carol"))

# Clue 6: The owner of the house numbered 6 does not live in a Mediterranean house.
solver.add(house_style_vars[6] != house_styles.index("mediterranean"))

# Clue 7: The person with the fish lives in a house with a higher number than Bob.
solver.add(Or([And(pet_vars[h1] == pets.index("fish"), name_vars[h2] == names.index("Bob"), h1 > h2) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 8: Eric lives in house number 6.
solver.add(name_vars[6] == names.index("Eric"))

# Clue 9: The person who owns the cat lives next door to the person who lives in a Victorian house.
solver.add(Or([And(pet_vars[h1] == pets.index("cat"), house_style_vars[h2] == house_styles.index("victorian"), Abs(h1 - h2) == 1) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 10: The person who lives in a Victorian house lives two houses away from the person with the hamster.
solver.add(Or([And(house_style_vars[h1] == house_styles.index("victorian"), pet_vars[h2] == pets.index("hamster"), Abs(h1 - h2) == 2) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 11: Arnold lives in a Craftsman house.
solver.add(Or([And(name_vars[h] == names.index("Arnold"), house_style_vars[h] == house_styles.index("craftsman")) for h in houses]))

# Clue 12: The Colonial house is to the left of the Modern house.
solver.add(Or([And(house_style_vars[h1] == house_styles.index("colonial"), house_style_vars[h2] == house_styles.index("modern"), h1 < h2) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 13: The person with the fish does not live in house number 2.
solver.add(pet_vars[2] != pets.index("fish"))

# Clue 14: Peter lives in a Colonial house.
solver.add(Or([And(name_vars[h] == names.index("Peter"), house_style_vars[h] == house_styles.index("colonial")) for h in houses]))

# Clue 15: The person born in January lives next door to the person born in April.
solver.add(Or([And(birthday_vars[h1] == birthdays.index("jan"), birthday_vars[h2] == birthdays.index("april"), Abs(h1 - h2) == 1) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 16: The person with the bird lives next door to the person who lives in a Modern house.
solver.add(Or([And(pet_vars[h1] == pets.index("bird"), house_style_vars[h2] == house_styles.index("modern"), Abs(h1 - h2) == 1) for h1 in houses for h2 in houses if h1 != h2]))

# Clue 17: Carol was born in March.
solver.add(birthday_vars[3] == birthdays.index("mar"))

# Clue 18: The owner of the house numbered 4 lives in a Craftsman house.
solver.add(house_style_vars[4] == house_styles.index("craftsman"))

# Clue 19: The owner of the house numbered 4 has a dog.
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