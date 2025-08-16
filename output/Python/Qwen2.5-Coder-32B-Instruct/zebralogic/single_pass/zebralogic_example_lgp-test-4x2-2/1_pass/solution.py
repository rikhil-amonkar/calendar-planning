import itertools
import json

def solve_puzzle():
    # Define the possible values
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["victorian", "ranch", "colonial", "craftsman"]
    houses = [1, 2, 3, 4]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            # Create a dictionary to map house number to attributes
            house_map = {house: {"Name": name, "HouseStyle": style} 
                         for house, name, style in zip(houses, name_perm, style_perm)}

            # Check the constraints
            if (house_map[3]["Name"] == "Eric" and
                house_map[3]["HouseStyle"] == "craftsman" and
                house_map[4]["Name"] == "Arnold" and
                house_map[house_map[2]["HouseStyle"] == "ranch"]["HouseStyle"] == "victorian" and
                house_map[house_map["HouseStyle"] == "victorian"]["Name"] == "Alice"):
                
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HouseStyle"],
                        "rows": [[str(house), house_map[house]["Name"], house_map[house]["HouseStyle"]] 
                                 for house in houses]
                    }
                }
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return

# Run the solver
solve_puzzle()