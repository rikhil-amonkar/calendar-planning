import itertools
import json

def solve_puzzle():
    # Define the variables
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    car_models = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for occupation_perm in itertools.permutations(occupations):
            for car_model_perm in itertools.permutations(car_models):
                # Create a dictionary to map house number to attributes
                house_dict = {house: {"name": name, "occupation": occupation, "car_model": car_model}
                              for house, name, occupation, car_model in zip(houses, name_perm, occupation_perm, car_model_perm)}

                # Check all constraints
                if (house_dict[5]["car_model"] == "ford f150" and
                    house_dict[2]["car_model"] != "chevrolet silverado" and
                    abs(house_dict[name_perm.index("Peter")]["house"] - house_dict[car_model_perm.index("honda civic")]["house"]) == 1 and
                    house_dict[5]["occupation"] != "lawyer" and
                    house_dict[name_perm.index("Carol")]["house"] > house_dict[name_perm.index("Eric")]["house"] and
                    house_dict[name_perm.index("Eric")]["occupation"] == "doctor" and
                    house_dict[name_perm.index("Arnold")]["occupation"] == "artist" and
                    house_dict[name_perm.index("Carol")]["house"] != 6 and
                    house_dict[name_perm.index("Bob")]["occupation"] == "engineer" and
                    house_dict[car_model_perm.index("toyota camry")]["occupation"] == "nurse" and
                    abs(house_dict[name_perm.index("Peter")]["house"] - house_dict[occupation_perm.index("lawyer")]["house"]) == 2 and
                    abs(house_dict[name_perm.index("Bob")]["house"] - house_dict[car_model_perm.index("tesla model 3")]["house"]) == 2 and
                    house_dict[name_perm.index("Carol")]["house"] > house_dict[name_perm.index("Eric")]["house"] and
                    house_dict[name_perm.index("teacher")]["house"] < house_dict[name_perm.index("nurse")]["house"]):

                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "CarModel"],
                            "rows": [[str(house), house_dict[house]["name"], house_dict[house]["occupation"], house_dict[house]["car_model"]] for house in houses]
                        }
                    }

                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return

# Call the function to solve the puzzle
solve_puzzle()