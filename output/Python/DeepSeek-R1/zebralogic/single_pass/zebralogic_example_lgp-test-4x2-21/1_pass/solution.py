import json

def main():
    # Initialize attributes for the 4 houses (0-indexed: index0=house1, index1=house2, etc.)
    names = [None] * 4
    styles = [None] * 4

    # Clue 1: Alice is in the second house
    names[1] = "Alice"
    
    # Clue 5: The person in a Craftsman-style house is Alice
    styles[1] = "craftsman"
    
    # Clue 2: Victorian house is directly left of Peter
    names[3] = "Peter"      # Peter must be in house4
    styles[2] = "victorian" # Victorian style is in house3 (left of Peter)
    
    # Clue 3: Peter is to the right of the ranch-style house
    styles[0] = "ranch"     # Ranch style must be in house1
    styles[3] = "colonial"  # Only remaining style for house4
    
    # Clue 4: Arnold is to the right of the Craftsman-style house (house2)
    names[2] = "Arnold"     # Arnold must be in house3
    names[0] = "Eric"       # Only remaining name for house1
    
    # Build the rows for the output
    rows = []
    for i in range(4):
        house_number = str(i + 1)
        row = [house_number, names[i], styles[i]]
        rows.append(row)
    
    # Create the solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()