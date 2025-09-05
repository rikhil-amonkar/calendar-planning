import json

def main():
    # Define the attributes
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]
    
    # Generate all possible combinations
    solutions = []
    for name1 in names:
        for food1 in foods:
            for mother1 in mothers:
                # House 2 must have different attributes
                name2 = [n for n in names if n != name1][0]
                food2 = [f for f in foods if f != food1][0]
                mother2 = [m for m in mothers if m != mother1][0]
                
                # Check constraints
                # Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
                clue1 = (food1 == "grilled cheese" and food2 == "pizza")
                
                # Clue 2: Arnold is not in the second house.
                clue2 = (name2 != "Arnold")
                
                # Clue 3: Arnold is the person whose mother's name is Holly.
                clue3 = True
                if name1 == "Arnold":
                    clue3 = (mother1 == "Holly")
                if name2 == "Arnold":
                    clue3 = (mother2 == "Holly")
                
                if clue1 and clue2 and clue3:
                    solutions.append([
                        ["1", name1, food1, mother1],
                        ["2", name2, food2, mother2]
                    ])
    
    # Format the solution
    if solutions:
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": solutions[0]
            }
        }
    else:
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": []
            }
        }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()