import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric"]
    car_models = ["toyota camry", "ford f150", "tesla model 3"]
    house_styles = ["ranch", "colonial", "victorian"]
    pets = ["cat", "dog", "fish"]
    occupations = ["engineer", "doctor", "teacher"]
    vacations = ["city", "mountain", "beach"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(car_models)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(pets)) * \
                       list(itertools.permutations(occupations)) * \
                       list(itertools.permutations(vacations))

    # Iterate through all possible combinations
    for names_perm, car_models_perm, house_styles_perm, pets_perm, occupations_perm, vacations_perm in all_permutations:
        # Create a list of dictionaries representing each house
        houses = [
            {"Name": names_perm[0], "CarModel": car_models_perm[0], "HouseStyle": house_styles_perm[0], "Pet": pets_perm[0], "Occupation": occupations_perm[0], "Vacation": vacations_perm[0]},
            {"Name": names_perm[1], "CarModel": car_models_perm[1], "HouseStyle": house_styles_perm[1], "Pet": pets_perm[1], "Occupation": occupations_perm[1], "Vacation": vacations_perm[1]},
            {"Name": names_perm[2], "CarModel": car_models_perm[2], "HouseStyle": house_styles_perm[2], "Pet": pets_perm[2], "Occupation": occupations_perm[2], "Vacation": vacations_perm[2]}
        ]

        # Check all the clues
        if (houses[0]["Pet"] == "fish" and
            houses[1]["CarModel"] == "toyota camry" and
            houses[1]["Vacation"] != "mountain" and
            houses[1]["Vacation"] != "city" and
            (houses[0]["Name"] == "Peter" or houses[0]["HouseStyle"] == "ranch") and
            houses[1]["HouseStyle"] == "colonial" and
            houses[0]["Pet"] == "cat" and
            (houses[0]["Name"] == "Eric" or houses[1]["Name"] == "Eric") and
            houses[2]["Occupation"] != "engineer" and
            (houses[0]["CarModel"] == "tesla model 3" or houses[1]["CarModel"] == "tesla model 3") and
            houses[2]["Pet"] == "dog" and
            houses[2]["Occupation"] == "engineer"):
            
            # If all clues are satisfied, format the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                    "rows": [
                        ["1", houses[0]["Name"], houses[0]["CarModel"], houses[0]["HouseStyle"], houses[0]["Pet"], houses[0]["Occupation"], houses[0]["Vacation"]],
                        ["2", houses[1]["Name"], houses[1]["CarModel"], houses[1]["HouseStyle"], houses[1]["Pet"], houses[1]["Occupation"], houses[1]["Vacation"]],
                        ["3", houses[2]["Name"], houses[2]["CarModel"], houses[2]["HouseStyle"], houses[2]["Pet"], houses[2]["Occupation"], houses[2]["Vacation"]]
                    ]
                }
            }
            print(json.dumps(solution))
            return

# Run the solver
solve_puzzle()