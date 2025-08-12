import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ["Peter", "Arnold", "Eric"]
    cars = ["toyota camry", "ford f150", "tesla model 3"]
    house_styles = ["ranch", "colonial", "victorian"]
    pets = ["cat", "dog", "fish"]
    occupations = ["engineer", "doctor", "teacher"]
    vacations = ["city", "mountain", "beach"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for car_perm in itertools.permutations(cars):
            for style_perm in itertools.permutations(house_styles):
                for pet_perm in itertools.permutations(pets):
                    for occ_perm in itertools.permutations(occupations):
                        for vac_perm in itertools.permutations(vacations):
                            # Assign permutations to houses
                            house_data = {
                                1: {"Name": name_perm[0], "Car": car_perm[0], "Style": style_perm[0], "Pet": pet_perm[0], "Occupation": occ_perm[0], "Vacation": vac_perm[0]},
                                2: {"Name": name_perm[1], "Car": car_perm[1], "Style": style_perm[1], "Pet": pet_perm[1], "Occupation": occ_perm[1], "Vacation": vac_perm[1]},
                                3: {"Name": name_perm[2], "Car": car_perm[2], "Style": style_perm[2], "Pet": pet_perm[2], "Occupation": occ_perm[2], "Vacation": vac_perm[2]}
                            }

                            # Check all clues
                            if (house_data[1]["Pet"] == "fish" and
                                house_data[2]["Car"] == "toyota camry" and
                                house_data[2]["Vacation"] != "mountain" and
                                house_data[2]["Vacation"] != "city" and
                                (house_data[1]["Style"] == "ranch" or (house_data[1]["Style"] != "ranch" and house_data[2]["Style"] == "ranch" and house_data[2]["Name"] != "Peter")) and
                                house_data[2]["Style"] == "colonial" and
                                house_data[1]["Pet"] == "cat" and
                                house_data[1]["Name"] == "Arnold" and
                                (house_data[1]["Name"] == "Eric" or house_data[2]["Name"] == "Eric") and
                                house_data[3]["Name"] != "Peter" and
                                (house_data[1]["Car"] == "tesla model 3" or house_data[2]["Car"] == "tesla model 3") and
                                house_data[1]["Occupation"] == "engineer" and
                                house_data[1]["Pet"] == "dog"):
                                
                                # Construct the solution in the required format
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Car", "Style", "Pet", "Occupation", "Vacation"],
                                        "rows": [
                                            [str(house), house_data[house]["Name"], house_data[house]["Car"], house_data[house]["Style"], house_data[house]["Pet"], house_data[house]["Occupation"], house_data[house]["Vacation"]]
                                            for house in houses
                                        ]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Run the solver and print the solution
print(solve_puzzle())