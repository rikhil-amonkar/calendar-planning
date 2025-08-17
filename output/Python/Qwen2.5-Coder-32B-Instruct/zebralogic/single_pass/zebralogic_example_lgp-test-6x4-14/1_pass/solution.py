import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
    car_models = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
    mothers = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
    hobbies = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

    for name_perm in itertools.permutations(names):
        for car_perm in itertools.permutations(car_models):
            for mother_perm in itertools.permutations(mothers):
                for hobby_perm in itertools.permutations(hobbies):
                    # Assign permutations to variables for easier access
                    name_map = dict(zip(houses, name_perm))
                    car_map = dict(zip(houses, car_perm))
                    mother_map = dict(zip(houses, mother_perm))
                    hobby_map = dict(zip(houses, hobby_perm))

                    # Apply clues
                    if (car_map[6] == "toyota camry" and
                        name_map[hobby_perm.index("photography")] == "Carol" and
                        mother_map[car_perm.index("chevrolet silverado")] == "Aniya" and
                        car_perm.index("chevrolet silverado") != 1 and
                        mother_map[car_perm.index("ford f150")] == "Sarah" and
                        name_map[mother_perm.index("Bob")] == "Bob" and
                        mother_map[6] == "Kailyn" and
                        name_perm.index("Eric") + 1 == name_perm.index(hobby_perm.index("knitting")) and
                        abs(mother_perm.index("Sarah") - car_perm.index("toyota camry")) == 1 and
                        mother_perm.index("Penny") > hobby_perm.index("knitting") and
                        mother_perm.index("Aniya") > car_perm.index("honda civic") and
                        name_perm.index("Alice") > car_perm.index("ford f150") and
                        name_map[hobby_perm.index("gardening")] == "Eric" and
                        hobby_perm.index("woodworking") < hobby_perm.index("knitting") and
                        abs(mother_perm.index("Sarah") - hobby_perm.index("cooking")) == 1 and
                        name_map[car_perm.index("honda civic")] == "Arnold" and
                        mother_perm.index("Holly") + 1 == hobby_perm.index("knitting")):
                        
                        # Construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            solution["solution"]["rows"].append([
                                str(house),
                                name_map[house],
                                car_map[house],
                                mother_map[house],
                                hobby_map[house]
                            ])
                        return json.dumps(solution, indent=2)

print(solve_puzzle())