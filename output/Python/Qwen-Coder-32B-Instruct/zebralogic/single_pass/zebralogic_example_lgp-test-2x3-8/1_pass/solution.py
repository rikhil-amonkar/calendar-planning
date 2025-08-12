import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]
    
    # Initialize the possible solutions
    solutions = []
    
    # Iterate over all permutations of names, birthdays, and mothers
    for name1 in names:
        for name2 in names:
            if name1 != name2:
                for birthday1 in birthdays:
                    for birthday2 in birthdays:
                        if birthday1 != birthday2:
                            for mother1 in mothers:
                                for mother2 in mothers:
                                    if mother1 != mother2:
                                        # Apply the clues
                                        clue1 = (name1 == "Eric" and mother2 == "Holly") or (name2 == "Eric" and mother1 == "Holly")
                                        clue2 = (birthday1 == "april" and name1 == "Eric") or (birthday1 == "april" and name1 == "Arnold")
                                        
                                        if clue1 and clue2:
                                            # If both clues are satisfied, add the solution
                                            solutions.append({
                                                "House": "1",
                                                "Name": name1,
                                                "Birthday": birthday1,
                                                "Mother": mother1
                                            })
                                            solutions.append({
                                                "House": "2",
                                                "Name": name2,
                                                "Birthday": birthday2,
                                                "Mother": mother2
                                            })
    
    # Format the solution as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": [
                [sol["House"], sol["Name"], sol["Birthday"], sol["Mother"]] for sol in solutions[:2]
            ]
        }
    }
    
    return json.dumps(result, indent=2)

# Output the solution
print(solve_puzzle())