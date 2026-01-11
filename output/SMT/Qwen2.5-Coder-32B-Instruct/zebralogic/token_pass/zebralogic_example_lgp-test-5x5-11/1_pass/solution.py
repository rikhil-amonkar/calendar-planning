from z3 import *

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the domains for each characteristic
names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
heights = ['average', 'very tall', 'very short', 'short', 'tall']
cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
phone_models = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

# Create variables for each characteristic for each house
name_vars = [Int(f'name_{i}') for i in houses]
height_vars = [Int(f'height_{i}') for i in houses]
cigar_vars = [Int(f'cigar_{i}') for i in houses]
smoothie_vars = [Int(f'smoothie_{i}') for i in houses]
phone_model_vars = [Int(f'phone_model_{i}') for i in houses]

# Create a solver instance
solver = Solver()

# Add constraints for unique values in each characteristic
solver.add(Distinct(name_vars))
solver.add(Distinct(height_vars))
solver.add(Distinct(cigar_vars))
solver.add(Distinct(smoothie_vars))
solver.add(Distinct(phone_model_vars))

# Map string values to integer indices for Z3
name_map = {name: idx for idx, name in enumerate(names)}
height_map = {height: idx for idx, height in enumerate(heights)}
cigar_map = {cigar: idx for idx, cigar in enumerate(cigars)}
smoothie_map = {smoothie: idx for idx, smoothie in enumerate(smoothies)}
phone_model_map = {phone_model: idx for idx, phone_model in enumerate(phone_models)}

# Add constraints based on clues
# Clue 1
solver.add(cigar_vars[smoothie_vars.index(name_map['desert'])] == cigar_map['prince'])

# Clue 2
alice_house = Int('alice_house')
eric_house = Int('eric_house')
solver.add(Or(Abs(alice_house - eric_house) == 1))
solver.add(And(1 <= alice_house, alice_house <= 5))
solver.add(And(1 <= eric_house, eric_house <= 5))
solver.add(name_vars[alice_house - 1] == name_map['Alice'])
solver.add(name_vars[eric_house - 1] == name_map['Eric'])

# Clue 3
short_house = Int('short_house')
blends_house = Int('blends_house')
solver.add(short_house == blends_house)
solver.add(height_vars[short_house - 1] == height_map['short'])
solver.add(cigar_vars[blends_house - 1] == cigar_map['blends'])

# Clue 4
iphone_13_house = Int('iphone_13_house')
blue_master_house = Int('blue_master_house')
solver.add(iphone_13_house + 1 == blue_master_house)
solver.add(phone_model_vars[iphone_13_house - 1] == phone_model_map['iphone 13'])
solver.add(cigar_vars[blue_master_house - 1] == cigar_map['blue master'])

# Clue 5
dunhill_house = Int('dunhill_house')
solver.add(dunhill_house == height_vars.index(height_map['average']))
solver.add(cigar_vars[dunhill_house - 1] == cigar_map['dunhill'])

# Clue 6
eric_tall_house = Int('eric_tall_house')
solver.add(eric_tall_house == height_vars.index(height_map['very tall']))
solver.add(name_vars[eric_tall_house - 1] == name_map['Eric'])

# Clue 7
arnold_house = Int('arnold_house')
huawei_p50_house = Int('huawei_p50_house')
solver.add(arnold_house + 1 == huawei_p50_house)
solver.add(name_vars[arnold_house - 1] == name_map['Arnold'])
solver.add(phone_model_vars[huawei_p50_house - 1] == phone_model_map['huawei p50'])

# Clue 8
bob_not_fourth_house = Int('bob_not_fourth_house')
solver.add(bob_not_fourth_house != 4)
solver.add(name_vars[bob_not_fourth_house - 1] == name_map['Bob'])

# Clue 9
eric_cherry_house = Int('eric_cherry_house')
cherry_house = Int('cherry_house')
solver.add(eric_cherry_house + 1 == cherry_house)
solver.add(name_vars[eric_cherry_house - 1] == name_map['Eric'])
solver.add(smoothie_vars[cherry_house - 1] == smoothie_map['cherry'])

# Clue 10
bob_dunhill_house = Int('bob_dunhill_house')
solver.add(bob_dunhill_house == cigar_vars.index(cigar_map['dunhill']))
solver.add(name_vars[bob_dunhill_house - 1] == name_map['Bob'])

# Clue 11
bob_dragonfruit_house = Int('bob_dragonfruit_house')
solver.add(bob_dragonfruit_house == smoothie_vars.index(smoothie_map['dragonfruit']))
solver.add(name_vars[bob_dragonfruit_house - 1] == name_map['Bob'])

# Clue 12
iphone_13_house = Int('iphone_13_house')
oneplus_9_house = Int('oneplus_9_house')
solver.add(Or(iphone_13_house + 1 == oneplus_9_house, iphone_13_house - 1 == oneplus_9_house))
solver.add(phone_model_vars[iphone_13_house - 1] == phone_model_map['iphone 13'])
solver.add(phone_model_vars[oneplus_9_house - 1] == phone_model_map['oneplus 9'])

# Clue 13
samsung_galaxy_s21_house = Int('samsung_galaxy_s21_house')
solver.add(samsung_galaxy_s21_house == height_vars.index(height_map['short']))
solver.add(phone_model_vars[samsung_galaxy_s21_house - 1] == phone_model_map['samsung galaxy s21'])

# Clue 14
very_tall_house = Int('very_tall_house')
dragonfruit_house = Int('dragonfruit_house')
solver.add(Abs(very_tall_house - dragonfruit_house) == 2)
solver.add(very_tall_house == height_vars.index(height_map['very tall']))
solver.add(dragonfruit_house == smoothie_vars.index(smoothie_map['dragonfruit']))

# Clue 15
eric_iphone_13_house = Int('eric_iphone_13_house')
solver.add(eric_iphone_13_house == phone_model_vars.index(phone_model_map['iphone 13']))
solver.add(name_vars[eric_iphone_13_house - 1] == name_map['Eric'])

# Clue 16
desert_house = Int('desert_house')
lime_house = Int('lime_house')
solver.add(desert_house < lime_house)
solver.add(smoothie_vars[desert_house - 1] == smoothie_map['desert'])
solver.add(smoothie_vars[lime_house - 1] == smoothie_map['lime'])

# Clue 17
arnold_short_house = Int('arnold_short_house')
solver.add(Or(arnold_short_house + 1 == short_house, arnold_short_house - 1 == short_house))
solver.add(name_vars[arnold_short_house - 1] == name_map['Arnold'])
solver.add(height_vars[short_house - 1] == height_map['very short'])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house - 1]].as_long()]
        height = heights[model[height_vars[house - 1]].as_long()]
        cigar = cigars[model[cigar_vars[house - 1]].as_long()]
        smoothie = smoothies[model[smoothie_vars[house - 1]].as_long()]
        phone_model = phone_models[model[phone_model_vars[house - 1]].as_long()]
        solution.append([str(house), name, height, cigar, smoothie, phone_model])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")