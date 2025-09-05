import json
from itertools import permutations

def main():
    # Define the attributes
    names = ["Eric", "Arnold", "Alice", "Peter"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]
    houses = [1, 2, 3, 4]
    
    # Generate all possible assignments
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            assignment = list(zip(houses, name_perm, style_perm))
            
            # Check clue 1: Alice is in the second house
            if assignment[1][1] != "Alice":
                continue
                
            # Check clue 5: The person in a Craftsman-style house is Alice
            if not any(h[1] == "Alice" and h[2] == "craftsman" for h in assignment):
                continue
                
            # Check clue 2: Victorian house is directly left of Peter
            peter_house = None
            victorian_house = None
            for h in assignment:
                if h[1] == "Peter":
                    peter_house = h[0]
                if h[2] == "victorian":
                    victorian_house = h[0]
            
            if victorian_house is None or peter_house is None or victorian_house + 1 != peter_house:
                continue
                
            # Check clue 3: Peter is right of ranch-style home
            ranch_house = None
            for h in assignment:
                if h[2] == "ranch":
                    ranch_house = h[0]
            
            if ranch_house is None or peter_house <= ranch_house:
                continue
                
            # Check clue 4: Arnold is right of Craftsman-style house
            craftsman_house = None
            arnold_house = None
            for h in assignment:
                if h[2] == "craftsman":
                    craftsman_house = h[0]
                if h[1] == "Arnold":
                    arnold_house = h[0]
            
            if craftsman_house is None or arnold_house is None or arnold_house <= craftsman_house:
                continue
                
            # Found valid solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "HouseStyle"],
                    "rows": [
                        [str(h[0]), h[1], h[2]] for h in assignment
                    ]
                }
            }
            
            print(json.dumps(solution))
            return
    
    # If no solution found (shouldn't happen with valid puzzle)
    print(json.dumps({"solution": {"header": ["House", "Name", "HouseStyle"], "rows": []}}))

if __name__ == "__main__":
    main()