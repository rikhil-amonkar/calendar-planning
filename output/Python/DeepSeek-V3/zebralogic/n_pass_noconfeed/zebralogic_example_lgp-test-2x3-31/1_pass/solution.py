import json

def main():
    # Define the attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]
    
    # Initialize all possible assignments
    for name1 in names:
        for sport1 in sports:
            for hobby1 in hobbies:
                # For house 1
                # Remaining attributes for house 2
                name2 = [n for n in names if n != name1][0]
                sport2 = [s for s in sports if s != sport1][0]
                hobby2 = [h for h in hobbies if h != hobby1][0]
                
                # Check all constraints
                # Clue 1: The person who enjoys gardening is Arnold.
                gardening_arnold = True
                if hobby1 == "gardening" and name1 != "Arnold":
                    gardening_arnold = False
                if hobby2 == "gardening" and name2 != "Arnold":
                    gardening_arnold = False
                if not gardening_arnold:
                    continue
                
                # Clue 2: The photography enthusiast is not in the first house.
                if hobby1 == "photography":
                    continue
                
                # Clue 3: The person who loves soccer is not in the first house.
                if sport1 == "soccer":
                    continue
                
                # If we reach here, all constraints are satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "FavoriteSport", "Hobby"],
                        "rows": [
                            ["1", name1, sport1, hobby1],
                            ["2", name2, sport2, hobby2]
                        ]
                    }
                }
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return
    
    # If no solution found (shouldn't happen with valid constraints)
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()