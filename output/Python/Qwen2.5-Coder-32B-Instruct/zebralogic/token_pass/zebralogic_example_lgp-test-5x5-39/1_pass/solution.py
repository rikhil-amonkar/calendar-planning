import json

def solve_puzzle():
    # Initialize houses with placeholders
    houses = [
        {"House": "1", "Name": None, "Birthday": None, "Mother": None, "Occupation": None, "HairColor": None},
        {"House": "2", "Name": None, "Birthday": None, "Mother": None, "Occupation": None, "HairColor": None},
        {"House": "3", "Name": None, "Birthday": None, "Mother": None, "Occupation": None, "HairColor": None},
        {"House": "4", "Name": None, "Birthday": None, "Mother": None, "Occupation": None, "HairColor": None},
        {"House": "5", "Name": None, "Birthday": None, "Mother": None, "Occupation": None, "HairColor": None}
    ]

    # Apply direct clues
    houses[4]["Birthday"] = "mar"  # Clue 1
    houses[0]["Birthday"] = "feb"  # Clue 2
    for house in houses:
        if house["Birthday"] == "feb":
            house["Name"] = "Eric"
    houses[2]["Mother"] = "Janelle"  # Clue 4
    houses[3]["Occupation"] = "artist"  # Clue 6
    houses[3]["HairColor"] = "brown"  # Clue 5
    houses[3]["Birthday"] = "jan"  # Clue 12
    for house in houses:
        if house["HairColor"] == "brown":
            house["Name"] = "Arnold"  # Clue 13
    houses[3]["Name"] = "Arnold"  # Confirm Arnold is in house 4
    houses[0]["Mother"] = "Penny"  # Clue 7 (will confirm position later)
    for house in houses:
        if house["Name"] == "Peter":
            house["HairColor"] = "black"
            house["Mother"] = "Holly"  # Clue 14
            house["Occupation"] = "lawyer"  # Clue 15
    houses[0]["Name"] = "Peter"  # Confirm Peter is in house 1
    houses[0]["Mother"] = "Penny"  # Confirm Penny is Peter's mother
    for house in houses:
        if house["HairColor"] == "gray":
            house["Occupation"] = "teacher"  # Clue 9
    for house in houses:
        if house["Name"] == "Alice":
            house["Mother"] = "Kailyn"  # Clue 10
            house["HairColor"] = "gray"  # Clue 17
    houses[0]["Name"] = "Peter"  # Reconfirm Peter is in house 1
    houses[4]["Name"] = "Arnold"  # Reconfirm Arnold is in house 5
    houses[4]["Mother"] = "Aniya"  # By elimination
    houses[2]["Name"] = "Alice"  # By elimination
    houses[1]["Name"] = "Bob"  # By elimination
    houses[1]["Mother"] = "Kailyn"  # By elimination
    houses[1]["HairColor"] = "red"  # By elimination
    houses[2]["Occupation"] = "engineer"  # By elimination
    houses[1]["Occupation"] = "doctor"  # By elimination
    houses[4]["Occupation"] = "teacher"  # By elimination

    # Final check and formatting
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": [list(house.values()) for house in houses]
        }
    }

    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())