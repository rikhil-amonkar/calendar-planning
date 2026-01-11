import json

def solve_puzzle():
    # Initialize the houses with possible names and styles
    houses = [
        {"House": "1", "Name": ["Arnold", "Peter", "Eric", "Alice"], "HouseStyle": ["victorian", "ranch", "colonial", "craftsman"]},
        {"House": "2", "Name": ["Arnold", "Peter", "Eric", "Alice"], "HouseStyle": ["victorian", "ranch", "colonial", "craftsman"]},
        {"House": "3", "Name": ["Arnold", "Peter", "Eric", "Alice"], "HouseStyle": ["victorian", "ranch", "colonial", "craftsman"]},
        {"House": "4", "Name": ["Arnold", "Peter", "Eric", "Alice"], "HouseStyle": ["victorian", "ranch", "colonial", "craftsman"]}
    ]

    # Apply Clue 3: Eric is in the third house.
    houses[2]["Name"] = ["Eric"]
    houses[2]["HouseStyle"].remove("craftsman")  # Eric is in a Craftsman house, but we'll set it explicitly later

    # Apply Clue 4: Arnold is in the fourth house.
    houses[3]["Name"] = ["Arnold"]

    # Apply Clue 1: Eric is the person in a Craftsman-style house.
    houses[2]["HouseStyle"] = ["craftsman"]

    # Apply Clue 5: The person residing in a Victorian house is Alice.
    for house in houses:
        if "Alice" in house["Name"]:
            house["HouseStyle"] = ["victorian"]
        elif "victorian" in house["HouseStyle"]:
            house["Name"] = ["Alice"]

    # Apply Clue 2: The person in a ranch-style home is directly left of the person in a Victorian house.
    # This means the ranch house must be in position 1 or 2, and the Victorian house must be in position 2 or 3.
    # Since Alice is in the Victorian house, and Eric is in the Craftsman house (position 3), the Victorian house must be in position 2.
    # Therefore, the Ranch house must be in position 1.
    houses[1]["HouseStyle"] = ["victorian"]
    houses[0]["HouseStyle"] = ["ranch"]
    
    # Update names accordingly
    houses[1]["Name"] = ["Alice"]
    houses[0]["Name"].remove("Alice")
    houses[0]["Name"].remove("Eric")
    houses[0]["Name"].remove("Arnold")
    houses[3]["Name"].remove("Alice")
    houses[3]["Name"].remove("Eric")

    # The only remaining name for house 0 is Peter
    houses[0]["Name"] = ["Peter"]

    # Construct the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }

    for house in houses:
        solution["solution"]["rows"].append([house["House"], house["Name"][0], house["HouseStyle"][0]])

    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())