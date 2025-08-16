from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4]
names = ['Eric', 'Peter', 'Arnold', 'Alice']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
heights = ['tall', 'average', 'short', 'very short']
phone_models = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

# Declare variables for each attribute
name_vars = {house: Int(f'name_{house}') for house in houses}
smoothie_vars = {house: Int(f'smoothie_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
phone_model_vars = {house: Int(f'phone_model_{house}') for house in houses}

# Add constraints for unique values per attribute
for attr_vars in [name_vars, smoothie_vars, cigar_vars, height_vars, phone_model_vars]:
    solver.add(Distinct(attr_vars.values()))

# Map string values to integers for Z3
name_map = {name: i for i, name in enumerate(names)}
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}
cigar_map = {cigar: i for i, cigar in enumerate(cigars)}
height_map = {height: i for i, height in enumerate(heights)}
phone_model_map = {phone_model: i for i, phone_model in enumerate(phone_models)}

# Add clues as constraints
# 1. The Dragonfruit smoothie lover is Eric.
solver.add(smoothie_vars[1] == smoothie_map['dragonfruit'])
solver.add(name_vars[1] == name_map['Eric'])

# 2. The Dunhill smoker is the person who likes Cherry smoothies.
solver.add(cigar_vars[2] == cigar_map['dunhill'])
solver.add(smoothie_vars[2] == smoothie_map['cherry'])

# 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
solver.add(phone_model_vars[1] == phone_model_map['samsung galaxy s21'])
solver.add(phone_model_vars[2] == phone_model_map['iphone 13'])

# 4. The Dunhill smoker is somewhere to the right of the person who is very short.
solver.add(Or(
    And(height_vars[1] == height_map['very short'], cigar_vars[2] == cigar_map['dunhill']),
    And(height_vars[1] == height_map['very short'], cigar_vars[3] == cigar_map['dunhill']),
    And(height_vars[1] == height_map['very short'], cigar_vars[4] == cigar_map['dunhill']),
    And(height_vars[2] == height_map['very short'], cigar_vars[3] == cigar_map['dunhill']),
    And(height_vars[2] == height_map['very short'], cigar_vars[4] == cigar_map['dunhill']),
    And(height_vars[3] == height_map['very short'], cigar_vars[4] == cigar_map['dunhill'])
))

# 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
solver.add(Or(
    And(smoothie_vars[1] == smoothie_map['desert'], smoothie_vars[2] == smoothie_map['watermelon']),
    And(smoothie_vars[1] == smoothie_map['desert'], smoothie_vars[3] == smoothie_map['watermelon']),
    And(smoothie_vars[1] == smoothie_map['desert'], smoothie_vars[4] == smoothie_map['watermelon']),
    And(smoothie_vars[2] == smoothie_map['desert'], smoothie_vars[3] == smoothie_map['watermelon']),
    And(smoothie_vars[2] == smoothie_map['desert'], smoothie_vars[4] == smoothie_map['watermelon']),
    And(smoothie_vars[3] == smoothie_map['desert'], smoothie_vars[4] == smoothie_map['watermelon'])
))

# 6. The Prince smoker is the person who uses a OnePlus 9.
solver.add(cigar_vars[3] == cigar_map['prince'])
solver.add(phone_model_vars[3] == phone_model_map['oneplus 9'])

# 7. The person who is tall is in the third house.
solver.add(height_vars[3] == height_map['tall'])

# 8. The person who is very short is the person who uses an iPhone 13.
solver.add(height_vars[2] == height_map['very short'])

# 9. The person who smokes Blue Master is not in the first house.
solver.add(cigar_vars[1] != cigar_map['blue master'])

# 10. The Dunhill smoker is the person who is short.
solver.add(cigar_vars[2] == cigar_map['dunhill'])
solver.add(height_vars[2] == height_map['short'])

# 11. Peter is not in the third house.
solver.add(name_vars[3] != name_map['Peter'])

# 12. Arnold is the person who uses a Google Pixel 6.
solver.add(name_vars[1] == name_map['Arnold'])
solver.add(phone_model_vars[1] == phone_model_map['google pixel 6'])

# 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
solver.add(smoothie_vars[1] == smoothie_map['dragonfruit'])
solver.add(cigar_vars[1] == cigar_map['pall mall'])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        smoothie = smoothies[model[smoothie_vars[house]].as_long()]
        cigar = cigars[model[cigar_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        phone_model = phone_models[model[phone_model_vars[house]].as_long()]
        solution.append([str(house), name, smoothie, cigar, height, phone_model])
    
    print({
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": solution
        }
    })
else:
    print("No solution found")