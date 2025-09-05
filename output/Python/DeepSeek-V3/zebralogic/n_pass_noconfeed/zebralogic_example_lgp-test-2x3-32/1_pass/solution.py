import json

def main():
    # Define the attributes
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]
    
    # Define the houses
    houses = [1, 2]
    
    # Initialize all possible assignments
    solutions = []
    
    # Generate all possible permutations
    for name1 in names:
        for bday1 in birthdays:
            for color1 in colors:
                # Assign remaining values to house 2
                name2 = [n for n in names if n != name1][0]
                bday2 = [b for b in birthdays if b != bday1][0]
                color2 = [c for c in colors if c != color1][0]
                
                solution = {
                    1: {"Name": name1, "Birthday": bday1, "Color": color1},
                    2: {"Name": name2, "Birthday": bday2, "Color": color2}
                }
                solutions.append(solution)
    
    # Apply constraints
    valid_solutions = []
    for solution in solutions:
        # Clue 1: Eric loves yellow
        eric_house = None
        for house, attrs in solution.items():
            if attrs["Name"] == "Eric":
                eric_house = house
                break
        
        if eric_house is None or solution[eric_house]["Color"] != "yellow":
            continue
        
        # Clue 2: April birthday in first house
        if solution[1]["Birthday"] != "april":
            continue
        
        # Clue 3: Yellow lover not in first house
        if solution[1]["Color"] == "yellow":
            continue
        
        valid_solutions.append(solution)
    
    # There should be exactly one valid solution
    if len(valid_solutions) != 1:
        raise ValueError("No unique solution found")
    
    solution = valid_solutions[0]
    
    # Format the output
    header = ["House", "Name", "Birthday", "Color"]
    rows = []
    
    for house in sorted(solution.keys()):
        attrs = solution[house]
        row = [str(house), attrs["Name"], attrs["Birthday"], attrs["Color"]]
        rows.append(row)
    
    # Create the JSON output
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()