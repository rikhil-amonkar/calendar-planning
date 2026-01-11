import json

# Initialize the houses with all possible values
houses = [
    {"house": "1", "name": ["Eric", "Arnold", "Peter"], "vacation": ["mountain", "city", "beach"], 
     "height": ["very short", "average", "short"], "flower": ["carnations", "daffodils", "lilies"], 
     "hair_color": ["brown", "black", "blonde"], "education": ["associate", "bachelor", "high school"]},
    {"house": "2", "name": ["Eric", "Arnold", "Peter"], "vacation": ["mountain", "city", "beach"], 
     "height": ["very short", "average", "short"], "flower": ["carnations", "daffodils", "lilies"], 
     "hair_color": ["brown", "black", "blonde"], "education": ["associate", "bachelor", "high school"]},
    {"house": "3", "name": ["Eric", "Arnold", "Peter"], "vacation": ["mountain", "city", "beach"], 
     "height": ["very short", "average", "short"], "flower": ["carnations", "daffodils", "lilies"], 
     "hair_color": ["brown", "black", "blonde"], "education": ["associate", "bachelor", "high school"]}
]

# Apply direct clues
# Clue 1: Peter is the person who has an average height.
for house in houses:
    if "Peter" in house["name"]:
        house["name"] = ["Peter"]
        house["height"] = ["average"]

# Clue 2: The person who loves a bouquet of daffodils is Arnold.
for house in houses:
    if "Arnold" in house["name"]:
        house["name"] = ["Arnold"]
        house["flower"] = ["daffodils"]

# Clue 4: The person who loves beach vacations is in the first house.
houses[0]["vacation"] = ["beach"]

# Clue 5: The person with a high school diploma is in the third house.
houses[2]["education"] = ["high school"]

# Clue 7: The person who loves the boquet of lilies is Eric.
for house in houses:
    if "Eric" in house["name"]:
        house["name"] = ["Eric"]
        house["flower"] = ["lilies"]

# Clue 8: The person who loves the boquet of lilies is the person with a bachelor's degree.
for house in houses:
    if "lilies" in house["flower"]:
        house["education"] = ["bachelor"]

# Clue 10: The person who has blonde hair is in the third house.
houses[2]["hair_color"] = ["blonde"]

# Clue 11: The person who loves beach vacations is the person who has brown hair.
for house in houses:
    if "beach" in house["vacation"]:
        house["hair_color"] = ["brown"]

# Apply elimination based on clues
# Clue 3: The person who is very short is not in the second house.
houses[1]["height"].remove("very short")

# Clue 6: The person who is short is somewhere to the right of the person who is very short.
# This means the person who is very short must be in house 1 or 2, and the person who is short must be in house 2 or 3.
if "very short" in houses[0]["height"]:
    houses[2]["height"].remove("very short")
elif "very short" in houses[1]["height"]:
    houses[0]["height"].remove("very short")
    houses[2]["height"].remove("very short")

# Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
# This means Peter cannot be in the last house.
for house in houses:
    if "Peter" in house["name"]:
        if house["house"] == "3":
            raise ValueError("Peter cannot be in the third house based on clue 9.")
        elif house["house"] == "2":
            houses[0]["vacation"].remove("city")
        elif house["house"] == "1":
            houses[0]["vacation"].remove("city")
            houses[1]["vacation"].remove("city")

# Final deduction
def deduce(houses):
    while True:
        changed = False
        for house in houses:
            for key, values in house.items():
                if len(values) == 1:
                    value = values[0]
                    for other_house in houses:
                        if other_house != house and key in other_house and value in other_house[key]:
                            other_house[key].remove(value)
                            changed = True
        if not changed:
            break

deduce(houses)

# Assign remaining single values
for house in houses:
    for key, values in house.items():
        if len(values) == 1:
            house[key] = values[0]

# Prepare the solution in the required JSON format
solution = {
    "solution": {
        "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
        "rows": []
    }
}

for house in houses:
    solution["solution"]["rows"].append([
        house["house"], house["name"], house["vacation"], house["height"], 
        house["flower"], house["hair_color"], house["education"]
    ])

print(json.dumps(solution, indent=2))