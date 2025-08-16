import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2]

# Define variables for each attribute in each house
name = {house: String(f"name_{house}") for house in houses}
favorite_sport = {house: String(f"sport_{house}") for house in houses}
hair_color = {house: String(f"hair_{house}") for house in houses}
height = {house: String(f"height_{house}") for house in houses}
smoothie = {house: String(f"smoothie_{house}") for house in houses}
flower = {house: String(f"flower_{house}") for house in houses}

# Define the possible values for each attribute
names = ["Arnold", "Eric"]
sports = ["basketball", "soccer"]  # Note: "basketball" is misspelled as "basketball" in the problem statement
hair_colors = ["brown", "black"]
heights = ["very short", "short"]
smoothies = ["desert", "cherry"]  # Note: "desert" is likely a typo for "dessert", but we'll use as given
flowers = ["daffodils", "carnations"]

# Add constraints that each attribute in each house must be one of the allowed values
for house in houses:
    s.add(Or([name[house] == n for n in names]))
    s.add(Or([favorite_sport[house] == sp for sp in sports]))
    s.add(Or([hair_color[house] == hc for hc in hair_colors]))
    s.add(Or([height[house] == ht for ht in heights]))
    s.add(Or([smoothie[house] == sm for sm in smoothies]))
    s.add(Or([flower[house] == fl for fl in flowers]))

# Add uniqueness constraints for each attribute across houses
for attr in [name, favorite_sport, hair_color, height, smoothie, flower]:
    s.add(Distinct([attr[house] for house in houses]))

# Clue 1: The person who loves soccer is not in the second house.
s.add(favorite_sport[2] != "soccer")

# Clue 2: The Desert smoothie lover is directly left of the person who is very short.
# This means house 1 has desert smoothie and house 2 is very short, or it's not possible (since there are only 2 houses)
s.add(Or(
    And(smoothie[1] == "desert", height[2] == "very short"),
    And(smoothie[2] == "desert", height[1] == "very short")  # This would require a house 3, which doesn't exist
))
# Since there are only 2 houses, the only possible is house 1 has desert and house 2 is very short
s.add(smoothie[1] == "desert")
s.add(height[2] == "very short")

# Clue 3: The person who is very short is the person who has brown hair.
s.add(hair_color[2] == "brown")

# Clue 4: The person who loves carnations is the Desert smoothie lover.
# Since house 1 has desert smoothie, house 1 must have carnations
s.add(flower[1] == "carnations")

# Clue 5: Eric and the person who has brown hair are next to each other.
# Brown hair is in house 2, so Eric must be in house 1
s.add(name[1] == "Eric")
# Therefore, Arnold is in house 2
s.add(name[2] == "Arnold")

# Check if the model is satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": []
        }
    }
    for house in houses:
        row = [
            str(house),
            model.eval(name[house]).as_string(),
            model.eval(favorite_sport[house]).as_string(),
            model.eval(hair_color[house]).as_string(),
            model.eval(height[house]).as_string(),
            model.eval(smoothie[house]).as_string(),
            model.eval(flower[house]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")