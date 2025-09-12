from z3 import *
import json

solver = Solver()

# Define the attributes and their possible values
attributes = {
    'Name': ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold'],
    'PhoneModel': ['oneplus 9', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'huawei p50'],
    'Cigar': ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster'],
    'Flower': ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris'],
    'Color': ['yellow', 'red', 'green', 'blue', 'white', 'purple'],
    'FavoriteSport': ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']
}

# For each attribute, create variables for each house (1-6)
# Each variable is an integer between 0 and 5, representing the index in the attribute's value list
attr_vars = {}
for attr, values in attributes.items():
    attr_vars[attr] = [Int(f"{attr}_{i+1}") for i in range(6)]
    for v in attr_vars[attr]:
        solver.add(And(v >= 0, v <= 5))
    solver.add(Distinct(attr_vars[attr]))

# Create variables for the position of each attribute value
value_position_vars = {}

for attr, values in attributes.items():
    value_position_vars[attr] = {}
    for idx, value in enumerate(values):
        var_name = f"{attr}_pos_{value.replace(' ', '_')}"
        value_position_vars[attr][value] = Int(var_name)
        pos_var = value_position_vars[attr][value]
        solver.add(attr_vars[attr][pos_var] == idx)

# Add all the clue constraints using value_position_vars

# Clue 1: The person who uses a OnePlus 9 is in the second house.
solver.add(value_position_vars['PhoneModel']['oneplus 9'] == 1)

# Clue 2: Xiaomi Mi 11 is to the left of Huawei P50.
i_xiaomi = value_position_vars['PhoneModel']['xiaomi mi 11']
i_huawei = value_position_vars['PhoneModel']['huawei p50']
solver.add(i_xiaomi < i_huawei)

# Clue 3: Carol is the person who loves carnations.
pos_carol = value_position_vars['Name']['Carol']
pos_carnations = value_position_vars['Flower']['carnations']
solver.add(pos_carol == pos_carnations)

# Clue 4: The person who loves purple is directly left of Pall Mall smoker.
pos_purple = value_position_vars['Color']['purple']
pos_pall_mall = value_position_vars['Cigar']['pall mall']
solver.add(pos_pall_mall == pos_purple + 1)

# Clue 5: The person whose favorite color is green is the one who smokes Blue Master.
pos_green = value_position_vars['Color']['green']
pos_blue_master = value_position_vars['Cigar']['blue master']
solver.add(pos_green == pos_blue_master)

# Clue 6: The person who loves yellow and blue are next to each other.
pos_yellow = value_position_vars['Color']['yellow']
pos_blue = value_position_vars['Color']['blue']
solver.add(Or(pos_yellow == pos_blue + 1, pos_blue == pos_yellow + 1))

# Clue 7: Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
pos_eric = value_position_vars['Name']['Eric']
pos_samsung = value_position_vars['PhoneModel']['samsung galaxy s21']
solver.add(pos_eric > pos_samsung)

# Clue 8: Two houses between Carol and daffodils.
pos_daffodils = value_position_vars['Flower']['daffodils']
solver.add(Or(pos_daffodils == pos_carol + 3, pos_carol == pos_daffodils + 3))

# Clue 9: Prince smoker is the person who loves basketball.
pos_prince = value_position_vars['Cigar']['prince']
pos_basketball = value_position_vars['FavoriteSport']['basketball']
solver.add(pos_prince == pos_basketball)

# Clue 10: Dunhill smoker is the person who loves volleyball.
pos_dunhill = value_position_vars['Cigar']['dunhill']
pos_volleyball = value_position_vars['FavoriteSport']['volleyball']
solver.add(pos_dunhill == pos_volleyball)

# Clue 11: The person who loves swimming is the one who uses Google Pixel 6.
pos_swimming = value_position_vars['FavoriteSport']['swimming']
pos_google = value_position_vars['PhoneModel']['google pixel 6']
solver.add(pos_swimming == pos_google)

# Clue 12: The person who uses a Huawei P50 is directly left of the person who loves white.
pos_huawei = value_position_vars['PhoneModel']['huawei p50']
pos_white = value_position_vars['Color']['white']
solver.add(pos_white == pos_huawei + 1)

# Clue 13: The person who uses a OnePlus 9 (house 2, which is pos=1) and the person who loves roses are next to each other.
pos_roses = value_position_vars['Flower']['roses']
solver.add(Or(pos_roses == 1 + 1, pos_roses == 1 - 1))

# Clue 14: The person who loves iris is to the left of Eric.
pos_iris = value_position_vars['Flower']['iris']
solver.add(pos_iris < pos_eric)

# Clue 15: Dunhill smoker is Peter.
pos_peter = value_position_vars['Name']['Peter']
solver.add(pos_dunhill == pos_peter)

# Clue 16: The person who loves blue is Peter.
pos_blue = value_position_vars['Color']['blue']
solver.add(pos_blue == pos_peter)

# Clue 17: The person who loves tulips is Bob.
pos_tulips = value_position_vars['Flower']['tulips']
pos_bob = value_position_vars['Name']['Bob']
solver.add(pos_tulips == pos_bob)

# Clue 18: Alice is in the first house.
pos_alice = value_position_vars['Name']['Alice']
solver.add(pos_alice == 0)

# Clue 19: The person who loves baseball is directly left of the Blue Master smoker.
pos_baseball = value_position_vars['FavoriteSport']['baseball']
solver.add(pos_blue_master == pos_baseball + 1)

# Clue 20: The person who uses Google Pixel 6 is to the right of the person who smokes blends.
pos_blends = value_position_vars['Cigar']['blends']
solver.add(pos_google > pos_blends)

# Clue 21: The person who loves soccer is Carol.
pos_soccer = value_position_vars['FavoriteSport']['soccer']
solver.add(pos_soccer == pos_carol)

# Clue 22: The person who loves carnations is directly left of the person who smokes blends.
solver.add(pos_blends == pos_carnations + 1)

# Clue 23: Eric is the person who smokes blends.
solver.add(pos_eric == pos_blends)

# Clue 24: The person who loves volleyball is the one who uses iPhone 13.
pos_iphone = value_position_vars['PhoneModel']['iphone 13']
solver.add(pos_volleyball == pos_iphone)

# Now, check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house_num in range(1, 7):
        house_index = house_num - 1
        name_idx = model.evaluate(attr_vars['Name'][house_index]).as_long()
        phone_idx = model.evaluate(attr_vars['PhoneModel'][house_index]).as_long()
        cigar_idx = model.evaluate(attr_vars['Cigar'][house_index]).as_long()
        flower_idx = model.evaluate(attr_vars['Flower'][house_index]).as_long()
        color_idx = model.evaluate(attr_vars['Color'][house_index]).as_long()
        sport_idx = model.evaluate(attr_vars['FavoriteSport'][house_index]).as_long()

        name = attributes['Name'][name_idx]
        phone = attributes['PhoneModel'][phone_idx]
        cigar = attributes['Cigar'][cigar_idx]
        flower = attributes['Flower'][flower_idx]
        color = attributes['Color'][color_idx]
        sport = attributes['FavoriteSport'][sport_idx]

        solution.append([str(house_num), name, phone, cigar, flower, color, sport])

    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")