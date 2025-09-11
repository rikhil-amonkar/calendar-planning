import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(houses))
    
    for name_perm in permutations:
        for mother_perm in permutations:
            for height_perm in permutations:
                # Create a dictionary to map each house to its attributes
                house_dict = {house: {"Name": name, "Mother": mother, "Height": height}
                              for house, name, mother, height in zip(houses, name_perm, mother_perm, height_perm)}
                
                # Find the houses based on specific conditions
                alice_house = next((house for house, details in house_dict.items() if details["Name"] == "Alice"), None)
                average_height_house = next((house for house, details in house_dict.items() if details["Height"] == "average"), None)
                penny_mother_house = next((house for house, details in house_dict.items() if details["Mother"] == "Penny"), None)
                janelle_mother_house = next((house for house, details in house_dict.items() if details["Mother"] == "Janelle"), None)
                peter_house = next((house for house, details in house_dict.items() if details["Name"] == "Peter"), None)
                short_height_house = next((house for house, details in house_dict.items() if details["Height"] == "short"), None)
                arnold_house = next((house for house, details in house_dict.items() if details["Name"] == "Arnold"), None)
                very_tall_height_house = next((house for house, details in house_dict.items() if details["Height"] == "very tall"), None)
                bob_house = next((house for house, details in house_dict.items() if details["Name"] == "Bob"), None)
                eric_house = next((house for house, details in house_dict.items() if details["Name"] == "Eric"), None)
                
                # Check all the clues
                if (alice_house is not None and house_dict[alice_house]["Mother"] == "Aniya" and
                    average_height_house is not None and penny_mother_house is not None and average_height_house < penny_mother_house and
                    janelle_mother_house is not None and house_dict[janelle_mother_house]["Name"] == "Bob" and
                    peter_house is not None and peter_house != 2 and
                    short_height_house is not None and arnold_house is not None and short_height_house + 1 == arnold_house and
                    very_tall_height_house is not None and house_dict[very_tall_height_house]["Name"] == "Arnold" and
                    bob_house is not None and average_height_house is not None and bob_house + 1 == average_height_house and
                    eric_house is not None and eric_house != 5 and
                    house_dict[eric_house]["Mother"] == "Kailyn" and
                    house_dict[5]["Height"] == "very short"):
                    
                    # If all conditions are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Height"],
                            "rows": [[str(house), house_dict[house]["Name"], house_dict[house]["Mother"], house_dict[house]["Height"]]
                                     for house in houses]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())