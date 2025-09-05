import json

def main():
    # Define the attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]
    
    # Initialize all possible assignments
    for name_assignment in [(names[0], names[1]), (names[1], names[0])]:
        for food_assignment in [(foods[0], foods[1]), (foods[1], foods[0])]:
            # Check clue 1: The person who is a pizza lover is in the second house.
            if food_assignment[1] != "pizza":
                continue
                
            # Check clue 2: Arnold is not in the first house.
            if name_assignment[0] == "Arnold":
                continue
                
            # If we reach here, we found a valid assignment
            solution = {
                "solution": {
                    "header": ["House", "Name", "Food"],
                    "rows": [
                        ["1", name_assignment[0], food_assignment[0]],
                        ["2", name_assignment[1], food_assignment[1]]
                    ]
                }
            }
            
            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return
            
    # If no solution found (shouldn't happen with valid constraints)
    print(json.dumps({"solution": {"header": ["House", "Name", "Food"], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()