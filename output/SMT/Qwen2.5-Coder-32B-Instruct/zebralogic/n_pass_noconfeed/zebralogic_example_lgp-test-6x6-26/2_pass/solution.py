from z3 import *

# Define the domain of possible values
houses = range(1, 7)
names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
phone_models = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
colors = ["yellow", "red", "green", "blue", "white", "purple"]
favorite_sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

# Create a solver instance
solver = Solver()

# Declare variables
house_vars = {attr: [Int(f"{attr}_{i}") for i in houses] for attr in ["name", "phone_model", "cigar", "flower", "color", "favorite_sport"]}

# Add constraints for unique values per attribute
for attr, vars in house_vars.items():
    solver.add(Distinct(vars))

# Map names to integers
name_map = {name: i for i, name in enumerate(names)}
reverse_name_map = {i: name for i, name in enumerate(names)}

# Map phone models to integers
phone_model_map = {model: i for i, model in enumerate(phone_models)}
reverse_phone_model_map = {i: model for i, model in enumerate(phone_models)}

# Map cigars to integers
cigar_map = {cigar: i for i, cigar in enumerate(cigars)}
reverse_cigar_map = {i: cigar for i, cigar in enumerate(cigars)}

# Map flowers to integers
flower_map = {flower: i for i, flower in enumerate(flowers)}
reverse_flower_map = {i: flower for i, flower in enumerate(flowers)}

# Map colors to integers
color_map = {color: i for i, color in enumerate(colors)}
reverse_color_map = {i: color for i, color in enumerate(colors)}

# Map favorite sports to integers
favorite_sport_map = {sport: i for i, sport in enumerate(favorite_sports)}
reverse_favorite_sport_map = {i: sport for i, sport in enumerate(favorite_sports)}

# Helper function to create constraints
def constrain(attr, value, house):
    solver.add(house_vars[attr][house - 1] == value)

# Add constraints based on clues
constrain("phone_model", phone_model_map["oneplus 9"], 2)
# Corrected line: Use direct comparison instead of index
solver.add(house_vars["phone_model"][phone_model_map["xiaomi mi 11"]] < house_vars["phone_model"][phone_model_map["huawei p50"]])
constrain("flower", flower_map["carnations"], name_map["Carol"])
solver.add(house_vars["color"][color_map["purple"]] + 1 == house_vars["cigar"][cigar_map["pall mall"]])
solver.add(house_vars["cigar"][cigar_map["blue master"]] == house_vars["color"][color_map["green"]])
solver.add(Abs(house_vars["color"][color_map["yellow"]] - house_vars["color"][color_map["blue"]]) == 1)
solver.add(house_vars["name"][name_map["Eric"]] > house_vars["phone_model"][phone_model_map["samsung galaxy s21"]])
solver.add(Abs(house_vars["name"][name_map["Carol"]] - house_vars["flower"][flower_map["daffodils"]]) == 3)
constrain("cigar", cigar_map["prince"], favorite_sport_map["basketball"])
constrain("cigar", cigar_map["dunhill"], favorite_sport_map["volleyball"])
constrain("favorite_sport", favorite_sport_map["swimming"], phone_model_map["google pixel 6"])
solver.add(house_vars["color"][color_map["white"]] == house_vars["phone_model"][phone_model_map["huawei p50"]] + 1)
solver.add(Abs(house_vars["flower"][flower_map["roses"]] - house_vars["phone_model"][phone_model_map["oneplus 9"]]) == 1)
solver.add(house_vars["flower"][flower_map["iris"]] < house_vars["name"][name_map["Eric"]])
constrain("cigar", cigar_map["dunhill"], name_map["Peter"])
constrain("color", color_map["blue"], name_map["Peter"])
constrain("flower", flower_map["tulips"], name_map["Bob"])
constrain("name", name_map["Alice"], 1)
solver.add(house_vars["cigar"][cigar_map["blue master"]] + 1 == house_vars["favorite_sport"][favorite_sport_map["baseball"]])
solver.add(house_vars["cigar"][cigar_map["blends"]] < house_vars["phone_model"][phone_model_map["google pixel 6"]])
constrain("favorite_sport", favorite_sport_map["soccer"], name_map["Carol"])
solver.add(house_vars["cigar"][cigar_map["blends"]] == house_vars["flower"][flower_map["carnations"]] + 1)
constrain("cigar", cigar_map["blends"], name_map["Eric"])
constrain("favorite_sport", favorite_sport_map["volleyball"], phone_model_map["iphone 13"])

# Solve the puzzle
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        row = [
            str(house),
            reverse_name_map[model[house_vars["name"][house - 1]].as_long()],
            reverse_phone_model_map[model[house_vars["phone_model"][house - 1]].as_long()],
            reverse_cigar_map[model[house_vars["cigar"][house - 1]].as_long()],
            reverse_flower_map[model[house_vars["flower"][house - 1]].as_long()],
            reverse_color_map[model[house_vars["color"][house - 1]].as_long()],
            reverse_favorite_sport_map[model[house_vars["favorite_sport"][house - 1]].as_long()]
        ]
        solution.append(row)
    
    import json
    print(json.dumps({"solution": {"header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"], "rows": solution}}))
else:
    print("No solution found")