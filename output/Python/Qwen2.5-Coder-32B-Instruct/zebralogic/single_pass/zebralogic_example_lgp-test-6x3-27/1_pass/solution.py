import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for car_perm in itertools.permutations(cars):
                if (car_perm[4] == "ford f150" and
                    car_perm[1] != "chevrolet silverado" and
                    abs(name_perm.index("Peter") - car_perm.index("honda civic")) == 1 and
                    occ_perm[4] != "lawyer" and
                    occ_perm[car_perm.index("toyota camry")] == "nurse" and
                    name_perm.index("Carol") > name_perm.index("Eric") and
                    occ_perm[name_perm.index("Eric")] == "doctor" and
                    occ_perm.index("teacher") < occ_perm.index("nurse") and
                    name_perm[5] != "Carol" and
                    occ_perm[name_perm.index("Bob")] == "engineer" and
                    car_perm[occ_perm.index("nurse")] == "toyota camry" and
                    abs(name_perm.index("Peter") - occ_perm.index("lawyer")) == 2 and
                    abs(car_perm.index("tesla model 3") - name_perm.index("Bob")) == 2 and
                    occ_perm[name_perm.index("Arnold")] == "artist"):
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "CarModel"],
                            "rows": [
                                [str(houses[i]), name_perm[i], occ_perm[i], car_perm[i]] for i in range(6)
                            ]
                        }
                    }
                    return json.dumps(solution)

print(solve_puzzle())