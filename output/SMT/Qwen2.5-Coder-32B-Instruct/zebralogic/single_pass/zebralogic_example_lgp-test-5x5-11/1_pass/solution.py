from z3 import *

# Create variables for each characteristic
houses = range(1, 6)
names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
heights = ['average', 'very tall', 'very short', 'short', 'tall']
cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
phone_models = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

# Create dictionaries to map each characteristic to a variable
name_vars = {name: Int(name) for name in names}
height_vars = {height: Int(height) for height in heights}
cigar_vars = {cigar: Int(cigar) for cigar in cigars}
smoothie_vars = {smoothie: Int(smoothie) for smoothie in smoothies}
phone_model_vars = {phone_model: Int(phone_model) for phone_model in phone_models}

# Create solver instance
solver = Solver()

# Add constraints for each characteristic to be in a unique house
solver.add(Distinct([name_vars[name] for name in names]))
solver.add(Distinct([height_vars[height] for height in heights]))
solver.add(Distinct([cigar_vars[cigar] for cigar in cigars]))
solver.add(Distinct([smoothie_vars[smoothie] for smoothie in smoothies]))
solver.add(Distinct([phone_model_vars[phone_model] for phone_model in phone_models]))

# Add constraints for each house to be occupied by a unique person
for house in houses:
    solver.add(Or([name_vars[name] == house for name in names]))
    solver.add(Or([height_vars[height] == house for height in heights]))
    solver.add(Or([cigar_vars[cigar] == house for cigar in cigars]))
    solver.add(Or([smoothie_vars[smoothie] == house for smoothie in smoothies]))
    solver.add(Or([phone_model_vars[phone_model] == house for phone_model in phone_models]))

# Apply clues
# 1. The Prince smoker is the Desert smoothie lover.
solver.add(cigar_vars['prince'] == smoothie_vars['desert'])

# 2. There is one house between Eric and Alice.
solver.add(Abs(name_vars['Eric'] - name_vars['Alice']) == 2)

# 3. The person who is short is the person who smokes many unique blends.
solver.add(height_vars['short'] == cigar_vars['blends'])

# 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
solver.add(phone_model_vars['iphone 13'] + 1 == cigar_vars['blue master'])

# 5. The person who has an average height is the Dunhill smoker.
solver.add(height_vars['average'] == cigar_vars['dunhill'])

# 6. Eric is the person who is very tall.
solver.add(name_vars['Eric'] == height_vars['very tall'])

# 7. Arnold is directly left of the person who uses a Huawei P50.
solver.add(name_vars['Arnold'] + 1 == phone_model_vars['huawei p50'])

# 8. Bob is not in the fourth house.
solver.add(name_vars['Bob'] != 4)

# 9. Eric is directly left of the person who likes Cherry smoothies.
solver.add(name_vars['Eric'] + 1 == smoothie_vars['cherry'])

# 10. Bob is the Dunhill smoker.
solver.add(name_vars['Bob'] == cigar_vars['dunhill'])

# 11. The Dragonfruit smoothie lover is Bob.
solver.add(smoothie_vars['dragonfruit'] == name_vars['Bob'])

# 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
solver.add(Abs(phone_model_vars['iphone 13'] - phone_model_vars['oneplus 9']) == 1)

# 13. The person who uses a Samsung Galaxy S21 is the person who is short.
solver.add(phone_model_vars['samsung galaxy s21'] == height_vars['short'])

# 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
solver.add(Abs(name_vars['Eric'] - smoothie_vars['dragonfruit']) == 3)

# 15. The person who uses an iPhone 13 is Eric.
solver.add(phone_model_vars['iphone 13'] == name_vars['Eric'])

# 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
solver.add(smoothie_vars['desert'] < smoothie_vars['lime'])

# 17. Arnold and the person who is very short are next to each other.
solver.add(Abs(name_vars['Arnold'] - height_vars['very short']) == 1)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = [name for name in names if model.evaluate(name_vars[name]) == house][0]
        height = [height for height in heights if model.evaluate(height_vars[height]) == house][0]
        cigar = [cigar for cigar in cigars if model.evaluate(cigar_vars[cigar]) == house][0]
        smoothie = [smoothie for smoothie in smoothies if model.evaluate(smoothie_vars[smoothie]) == house][0]
        phone_model = [phone_model for phone_model in phone_models if model.evaluate(phone_model_vars[phone_model]) == house][0]
        solution.append([str(house), name, height, cigar, smoothie, phone_model])
    
    # Format the solution as required
    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")