from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
phone_models = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
houses = range(1, 7)

# Create dictionaries to map variables to their respective domains
name_vars = {house: Int(f'name_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
phone_model_vars = {house: Int(f'phone_model_{house}') for house in houses}

# Add constraints for unique assignments
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([phone_model_vars[house] for house in houses]))

# Map names, heights, and phone models to integers
name_map = {name: i for i, name in enumerate(names)}
height_map = {height: i for i, height in enumerate(heights)}
phone_model_map = {model: i for i, model in enumerate(phone_models)}

# Add constraints based on clues
# 1. Bob is directly left of the person who is tall.
solver.add(name_vars[1] == name_map['Bob'] ==>
           (name_vars[2] != name_map['Bob'] & height_vars[2] == height_map['tall']))
solver.add(name_vars[2] == name_map['Bob'] ==>
           (name_vars[3] != name_map['Bob'] & height_vars[3] == height_map['tall']))
solver.add(name_vars[3] == name_map['Bob'] ==>
           (name_vars[4] != name_map['Bob'] & height_vars[4] == height_map['tall']))
solver.add(name_vars[4] == name_map['Bob'] ==>
           (name_vars[5] != name_map['Bob'] & height_vars[5] == height_map['tall']))

# 2. Peter is somewhere to the left of the person who uses an iPhone 13.
solver.add(Or([And(phone_model_vars[i] == phone_model_map['iphone 13'], 
                   Or([name_vars[j] == name_map['Peter'] for j in range(1, i)])) for i in range(2, 7)]))

# 3. The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
solver.add(Or([And(phone_model_vars[i] == phone_model_map['google pixel 6'], 
                   Or([height_vars[j] == height_map['very short'] for j in range(i + 1, 7)])) for i in range(1, 6)]))

# 4. Carol is the person who is very tall.
solver.add(name_vars[1] == name_map['Carol'] ==> height_vars[1] == height_map['very tall'])
solver.add(name_vars[2] == name_map['Carol'] ==> height_vars[2] == height_map['very tall'])
solver.add(name_vars[3] == name_map['Carol'] ==> height_vars[3] == height_map['very tall'])
solver.add(name_vars[4] == name_map['Carol'] ==> height_vars[4] == height_map['very tall'])
solver.add(name_vars[5] == name_map['Carol'] ==> height_vars[5] == height_map['very tall'])
solver.add(name_vars[6] == name_map['Carol'] ==> height_vars[6] == height_map['very tall'])

# 5. There is one house between the person who uses a Google Pixel 6 and the person who is short.
solver.add(Or([And(phone_model_vars[i] == phone_model_map['google pixel 6'], 
                   height_vars[i + 2] == height_map['short']) for i in range(1, 5)]))

# 6. The person who uses a Samsung Galaxy S21 is not in the first house.
solver.add(phone_model_vars[1] != phone_model_map['samsung galaxy s21'])

# 7. The person who uses a OnePlus 9 is directly left of the person who is short.
solver.add(Or([And(phone_model_vars[i] == phone_model_map['oneplus 9'], 
                   height_vars[i + 1] == height_map['short']) for i in range(1, 6)]))

# 8. The person who is tall is Arnold.
solver.add(height_vars[1] == height_map['tall'] ==> name_vars[1] == name_map['Arnold'])
solver.add(height_vars[2] == height_map['tall'] ==> name_vars[2] == name_map['Arnold'])
solver.add(height_vars[3] == height_map['tall'] ==> name_vars[3] == name_map['Arnold'])
solver.add(height_vars[4] == height_map['tall'] ==> name_vars[4] == name_map['Arnold'])
solver.add(height_vars[5] == height_map['tall'] ==> name_vars[5] == name_map['Arnold'])
solver.add(height_vars[6] == height_map['tall'] ==> name_vars[6] == name_map['Arnold'])

# 9. The person who is super tall is in the first house.
solver.add(height_vars[1] == height_map['super tall'])

# 10. The person who uses a Xiaomi Mi 11 is Carol.
solver.add(phone_model_vars[1] == phone_model_map['xiaomi mi 11'] ==> name_vars[1] == name_map['Carol'])
solver.add(phone_model_vars[2] == phone_model_map['xiaomi mi 11'] ==> name_vars[2] == name_map['Carol'])
solver.add(phone_model_vars[3] == phone_model_map['xiaomi mi 11'] ==> name_vars[3] == name_map['Carol'])
solver.add(phone_model_vars[4] == phone_model_map['xiaomi mi 11'] ==> name_vars[4] == name_map['Carol'])
solver.add(phone_model_vars[5] == phone_model_map['xiaomi mi 11'] ==> name_vars[5] == name_map['Carol'])
solver.add(phone_model_vars[6] == phone_model_map['xiaomi mi 11'] ==> name_vars[6] == name_map['Carol'])

# 11. The person who uses a Google Pixel 6 is somewhere to the right of Eric.
solver.add(Or([And(phone_model_vars[i] == phone_model_map['google pixel 6'], 
                   Or([name_vars[j] == name_map['Eric'] for j in range(1, i)])) for i in range(2, 7)]))

# 12. The person who is short is in the sixth house.
solver.add(height_vars[6] == height_map['short'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        phone_model = phone_models[model[phone_model_vars[house]].as_long()]
        solution.append([str(house), name, height, phone_model])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "PhoneModel"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")