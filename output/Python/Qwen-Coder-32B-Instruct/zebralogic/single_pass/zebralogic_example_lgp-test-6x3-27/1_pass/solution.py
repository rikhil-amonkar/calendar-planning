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
                if (
                    # Clue 1
                    car_perm[4] == "ford f150" and
                    # Clue 2
                    car_perm[1] != "chevrolet silverado" and
                    # Clue 3
                    (abs(name_perm.index("Peter") - car_perm.index("honda civic")) == 1) and
                    # Clue 4
                    occ_perm[4] != "lawyer" and
                    # Clue 5
                    (name_perm.index(occ_perm.index("nurse")) + 1 == name_perm.index(occ_perm.index("artist"))) and
                    # Clue 6
                    name_perm.index("Eric") < name_perm.index("Carol") and
                    # Clue 7
                    occ_perm[name_perm.index("Eric")] == "doctor" and
                    # Clue 8
                    occ_perm.index("teacher") < occ_perm.index("nurse") and
                    # Clue 9
                    name_perm[5] != "Carol" and
                    # Clue 10
                    occ_perm[name_perm.index("Bob")] == "engineer" and
                    # Clue 11
                    car_perm[occ_perm.index("nurse")] == "toyota camry" and
                    # Clue 12
                    (abs(name_perm.index("Peter") - occ_perm.index("lawyer")) == 2) and
                    # Clue 13
                    (abs(car_perm.index("tesla model 3") - name_perm.index("Bob")) == 2) and
                    # Clue 14
                    occ_perm[name_perm.index("Arnold")] == "artist"
                ):
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "Car"],
                            "rows": []
                        }
                    }
                    for i in range(6):
                        solution["solution"]["rows"].append([
                            str(houses[i]),
                            name_perm[i],
                            occ_perm[i],
                            car_perm[i]
                        ])
                    return json.dumps(solution, indent=2)

print(solve_puzzle())