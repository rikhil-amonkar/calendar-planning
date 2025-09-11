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
                
                # Check all the clues
                if (house_dict[next(house for house, details in house_dict.items() if details["Name"] == "Alice")]["Mother"] == "Aniya" and
                    next(house for house, details in house_dict.items() if details["Height"] == "average") <
                    next(house for house, details in house_dict.items() if details["Mother"] == "Penny") and
                    house_dict[next(house for house, details in house_dict.items() if details["Mother"] == "Janelle")]["Name"] == "Bob" and
                    next(house for house, details in house_dict.items() if details["Name"] == "Peter") != 2 and
                    next(house for house, details in house_dict.items() if details["Height"] == "short") + 1 ==
                    next(house for house, details in house_dict.items() if details["Name"] == "Arnold") and
                    house_dict[next(house for house, details in house_dict.items() if details["Height"] == "very tall")]["Name"] == "Arnold" and
                    next(house for house, details in house_dict.items() if details["Name"] == "Bob") + 1 ==
                    next(house for house, details in house_dict.items() if details["Height"] == "average") and
                    next(house for house, details in house_dict.items() if details["Name"] == "Eric") != 5 and
                    house_dict[next(house for house, details in house_dict.items() if details["Name"] == "Eric")]["Mother"] == "Kailyn" and
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