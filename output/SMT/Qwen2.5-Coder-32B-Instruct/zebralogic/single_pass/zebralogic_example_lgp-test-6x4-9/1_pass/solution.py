from z3 import *

# Create the solver
solver = Solver()

# Define variables
houses = range(1, 7)
names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
phone_models = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']

# Create dictionaries to map variables to their respective domains
name_vars = {house: Int(f'name_{house}') for house in houses}
phone_model_vars = {house: Int(f'phone_model_{house}') for house in houses}
nationality_vars = {house: Int(f'nationality_{house}') for house in houses}
color_vars = {house: Int(f'color_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([phone_model_vars[house] for house in houses]))
solver.add(Distinct([nationality_vars[house] for house in houses]))
solver.add(Distinct([color_vars[house] for house in houses]))

# Map string values to integer codes
name_map = {name: i for i, name in enumerate(names)}
phone_model_map = {model: i for i, model in enumerate(phone_models)}
nationality_map = {nationality: i for i, nationality in enumerate(nationalities)}
color_map = {color: i for i, color in enumerate(colors)}

# Add clues as constraints
# 1. Carol is not in the third house.
solver.add(name_vars[3] != name_map['Carol'])

# 2. There is one house between the Dane and the British person.
dane_var = Int('dane')
brit_var = Int('brit')
solver.add(Or(dane_var + 2 == brit_var, dane_var - 2 == brit_var))
solver.add(Or([nationality_vars[house] == nationality_map['dane'] for house in houses]) == dane_var)
solver.add(Or([nationality_vars[house] == nationality_map['brit'] for house in houses]) == brit_var)

# 3. Carol is the person whose favorite color is green.
solver.add(And([Implies(name_vars[house] == name_map['Carol'], color_vars[house] == color_map['green']) for house in houses]))

# 4. Arnold is directly left of Alice.
solver.add(Or([And(name_vars[house] == name_map['Arnold'], name_vars[house + 1] == name_map['Alice']) for house in range(1, 6)]))

# 5. Alice is the German.
solver.add(And([Implies(name_vars[house] == name_map['Alice'], nationality_vars[house] == nationality_map['german']) for house in houses]))

# 6. The person who uses a OnePlus 9 is the person who loves purple.
solver.add(And([Implies(phone_model_vars[house] == phone_model_map['oneplus 9'], color_vars[house] == color_map['purple']) for house in houses]))

# 7. The person who uses a Huawei P50 is not in the third house.
solver.add(phone_model_vars[3] != phone_model_map['huawei p50'])

# 8. The person who uses a Samsung Galaxy S21 is in the fifth house.
solver.add(phone_model_vars[5] == phone_model_map['samsung galaxy s21'])

# 9. The person who loves white is somewhere to the right of the person whose favorite color is red.
red_var = Int('red')
white_var = Int('white')
solver.add(Or([color_vars[house] == color_map['red'] for house in houses]) == red_var)
solver.add(Or([color_vars[house] == color_map['white'] for house in houses]) == white_var)
solver.add(red_var < white_var)

# 10. The person who uses a Samsung Galaxy S21 is Bob.
solver.add(And([Implies(phone_model_vars[house] == phone_model_map['samsung galaxy s21'], name_vars[house] == name_map['Bob']) for house in houses]))

# 11. The Dane is the person who loves yellow.
solver.add(And([Implies(nationality_vars[house] == nationality_map['dane'], color_vars[house] == color_map['yellow']) for house in houses]))

# 12. The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
peter_var = Int('peter')
solver.add(Or([name_vars[house] == name_map['Peter'] for house in houses]) == peter_var)
solver.add(phone_model_vars[5] < peter_var)

# 13. The person who loves blue is Peter.
solver.add(And([Implies(color_vars[house] == color_map['blue'], name_vars[house] == name_map['Peter']) for house in houses]))

# 14. Peter is the British person.
solver.add(And([Implies(name_vars[house] == name_map['Peter'], nationality_vars[house] == nationality_map['brit']) for house in houses]))

# 15. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
solver.add(phone_model_vars[5] == phone_model_map['samsung galaxy s21'])
solver.add(phone_model_vars[6] == phone_model_map['iphone 13'])

# 16. The Norwegian is the person who loves purple.
solver.add(And([Implies(nationality_vars[house] == nationality_map['norwegian'], color_vars[house] == color_map['purple']) for house in houses]))

# 17. The person who uses a Xiaomi Mi 11 is the Chinese.
solver.add(And([Implies(phone_model_vars[house] == phone_model_map['xiaomi mi 11'], nationality_vars[house] == nationality_map['chinese']) for house in houses]))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        phone_model = phone_models[model[phone_model_vars[house]].as_long()]
        nationality = nationalities[model[nationality_vars[house]].as_long()]
        color = colors[model[color_vars[house]].as_long()]
        solution.append([str(house), name, phone_model, nationality, color])
    
    # Print the solution in JSON format
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found")