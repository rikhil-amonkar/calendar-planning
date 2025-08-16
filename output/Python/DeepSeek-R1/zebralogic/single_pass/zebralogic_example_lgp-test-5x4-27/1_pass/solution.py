import json

def main():
    houses = []
    for i in range(1, 6):
        houses.append({
            "House": str(i),
            "Name": None,
            "Birthday": None,
            "Cigar": None,
            "Drink": None
        })
    
    # Fixed assignments from clues
    houses[2]["Name"] = "Eric"      # Clue 13
    houses[2]["Drink"] = "root beer" # Clue 1
    houses[2]["Cigar"] = "pall mall" # Clue 2
    houses[1]["Birthday"] = "feb"    # Clue 8
    houses[1]["Cigar"] = "blends"    # Clue 7
    houses[2]["Birthday"] = "jan"    # Clue 6 (deduced)
    houses[4]["Name"] = "Peter"      # Clue 9 (deduced: Peter in house 5)
    houses[3]["Name"] = "Arnold"     # Clue 9 (Arnold in house 4)
    houses[1]["Drink"] = "tea"       # Clue 12 (tea in house 2)
    houses[3]["Drink"] = "coffee"    # Clue 12 (coffee in house 4)
    houses[3]["Cigar"] = "blue master" # Clue 11 (Blue Master with coffee)
    houses[0]["Drink"] = "milk"      # Clue 10 (milk not in house 5)
    houses[4]["Drink"] = "water"     # Remaining drink
    houses[0]["Name"] = "Bob"        # Clue 3 (Bob has April birthday)
    houses[0]["Birthday"] = "april"  # Clue 3
    houses[1]["Name"] = "Alice"      # Only name left
    houses[0]["Cigar"] = "prince"    # Remaining cigar
    houses[4]["Cigar"] = "dunhill"   # Dunhill for house 5
    houses[4]["Birthday"] = "mar"    # Clue 4 (Dunhill smoker has March birthday)
    houses[3]["Birthday"] = "sept"   # Last remaining birthday

    # Prepare the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            house["House"],
            house["Name"],
            house["Birthday"],
            house["Cigar"],
            house["Drink"]
        ]
        solution["solution"]["rows"].append(row)
    
    # Output as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()