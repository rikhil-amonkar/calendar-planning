import json

def main():
    # Initialize attributes for the four houses (index 0 to 3 represent houses 1 to 4)
    names = [None] * 4
    styles = [None] * 4
    
    # Apply clue 3: Eric is in the third house
    names[2] = "Eric"
    
    # Apply clue 4: Arnold is in the fourth house
    names[3] = "Arnold"
    
    # Apply clue 1: Eric is in a Craftsman-style house
    styles[2] = "craftsman"
    
    # Apply constraints from clue 2 and clue 5
    # Clue 2: Ranch is directly left of Victorian (so Victorian cannot be in house 1, and Ranch must be immediately left)
    # Clue 5: Victorian house is occupied by Alice
    
    # Determine position for Victorian style:
    #   - Cannot be house 1 (no house left for ranch)
    #   - Cannot be house 3 (already craftsman)
    #   - Cannot be house 4 (because ranch would need to be house 3, but house 3 is craftsman)
    # Therefore, Victorian must be in house 2
    styles[1] = "victorian"
    
    # Ranch must be directly left of Victorian (house 1)
    styles[0] = "ranch"
    
    # The only remaining style (colonial) must be in house 4
    styles[3] = "colonial"
    
    # Apply clue 5: The Victorian house (house 2) is Alice
    names[1] = "Alice"
    
    # The only remaining name (Peter) must be in house 1
    names[0] = "Peter"
    
    # Build the solution rows
    rows = []
    for i in range(4):
        house_num = str(i + 1)
        row = [house_num, names[i], styles[i]]
        rows.append(row)
    
    # Construct the solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    
    # Output as JSON
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()