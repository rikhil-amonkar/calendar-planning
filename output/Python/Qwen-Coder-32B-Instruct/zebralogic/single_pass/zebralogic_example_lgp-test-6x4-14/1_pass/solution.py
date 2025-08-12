import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
    cars = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
    mothers = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
    hobbies = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

    for name_perm in itertools.permutations(names):
        for car_perm in itertools.permutations(cars):
            for mother_perm in itertools.permutations(mothers):
                for hobby_perm in itertools.permutations(hobbies):
                    # Apply constraints
                    if (car_perm[5] == "toyota camry" and
                        name_perm[car_perm.index("toyota camry")] == "Carol" and
                        name_perm[car_perm.index("chevrolet silverado")] == name_perm[mother_perm.index("Aniya")] and
                        car_perm.index("chevrolet silverado") != 1 and
                        name_perm[car_perm.index("ford f150")] == name_perm[mother_perm.index("Sarah")] and
                        name_perm[car_perm.index("bmw 3 series")] == "Bob" and
                        mother_perm[5] == "Kailyn" and
                        name_perm.index("Eric") + 1 == name_perm.index(name_perm[hobby_perm.index("knitting")]) and
                        abs(mother_perm.index("Sarah") - car_perm.index("toyota camry")) == 1 and
                        mother_perm.index("Penny") > name_perm.index(name_perm[hobby_perm.index("knitting")]) and
                        mother_perm.index("Aniya") > name_perm.index(name_perm[car_perm.index("honda civic")]) and
                        name_perm.index("Alice") > name_perm.index(name_perm[car_perm.index("ford f150")]) and
                        name_perm[name_perm.index("Eric")] == name_perm[hobby_perm.index("gardening")] and
                        hobby_perm.index("woodworking") < hobby_perm.index("knitting") and
                        abs(mother_perm.index("Sarah") - hobby_perm.index("cooking")) == 1 and
                        name_perm[car_perm.index("honda civic")] == "Arnold" and
                        mother_perm.index("Holly") + 1 == name_perm.index(name_perm[hobby_perm.index("knitting")])):
                        
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Car", "Mother", "Hobby"],
                                "rows": []
                            }
                        }
                        for i in range(6):
                            solution["solution"]["rows"].append([
                                str(i+1),
                                name_perm[i],
                                car_perm[i],
                                mother_perm[i],
                                hobby_perm[i]
                            ])
                        return json.dumps(solution, indent=2)

print(solve_puzzle())