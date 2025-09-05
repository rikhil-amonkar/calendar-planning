import json

def main():
    # Initialize the houses
    houses = [
        {"House": "1", "Name": None, "Food": None, "Mother": None},
        {"House": "2", "Name": None, "Food": None, "Mother": None}
    ]
    
    # Available options for each attribute
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]
    
    # Apply clue 1: grilled cheese is directly left of pizza
    houses[0]["Food"] = "grilled cheese"
    houses[1]["Food"] = "pizza"
    foods.remove("grilled cheese")
    foods.remove("pizza")
    
    # Apply clue 2: Arnold is not in second house
    houses[0]["Name"] = "Arnold"
    names.remove("Arnold")
    
    # Apply clue 3: Arnold's mother is Holly
    houses[0]["Mother"] = "Holly"
    mothers.remove("Holly")
    
    # Assign remaining values to house 2
    houses[1]["Name"] = names[0]
    houses[1]["Mother"] = mothers[0]
    
    # Prepare the output structure
    solution = {
        "header": ["House", "Name", "Food", "Mother"],
        "rows": []
    }
    
    for house in houses:
        solution["rows"].append([
            house["House"],
            house["Name"],
            house["Food"],
            house["Mother"]
        ])
    
    # Output as JSON
    print(json.dumps({"solution": solution}, indent=2))

if __name__ == "__main__":
    main()