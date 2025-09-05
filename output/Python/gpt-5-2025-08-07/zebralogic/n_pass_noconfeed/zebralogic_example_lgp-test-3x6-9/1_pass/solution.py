import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2]  # indices for houses 1..3

    Names = ["Peter", "Arnold", "Eric"]
    CarModels = ["toyota camry", "ford f150", "tesla model 3"]
    HouseStyles = ["ranch", "colonial", "victorian"]
    Pets = ["cat", "dog", "fish"]
    Occupations = ["engineer", "doctor", "teacher"]
    Vacations = ["city", "mountain", "beach"]

    solutions = []

    # Generate Pets with constraint: fish in first house (index 0)
    for pet_perm_tail in itertools.permutations([p for p in Pets if p != "fish"], 2):
        pets = ["fish", pet_perm_tail[0], pet_perm_tail[1]]

        # Generate Cars with constraint: toyota camry in second house (index 1)
        for car_perm_tail in itertools.permutations([c for c in CarModels if c != "toyota camry"], 2):
            cars = [car_perm_tail[0], "toyota camry", car_perm_tail[1]]

            # Generate Styles
            for styles in itertools.permutations(HouseStyles, 3):
                # Clue 6: Camry directly left of Colonial
                try:
                    camry_idx = cars.index("toyota camry")
                    colonial_idx = styles.index("colonial")
                except ValueError:
                    continue
                if colonial_idx - camry_idx != 1:
                    continue

                # Generate Vacations with constraints: mountain not 2nd, city not 2nd
                # i.e., house 1 (index 1) cannot be city or mountain -> must be beach
                # The other two (index 0,2) are city and mountain in some order
                for vac_0_2 in itertools.permutations(["city", "mountain"], 2):
                    vacations = [vac_0_2[0], "beach", vac_0_2[1]]

                    # Generate Occupations with constraint: engineer not in third house (index 2)
                    for jobs in itertools.permutations(Occupations, 3):
                        if jobs[2] == "engineer":
                            continue

                        # Clue 11: dog owner is the engineer
                        if pets.index("dog") != jobs.index("engineer"):
                            continue

                        # Clue 10: Tesla left of Teacher
                        if cars.index("tesla model 3") >= jobs.index("teacher"):
                            continue

                        # Generate Names
                        for names in itertools.permutations(Names, 3):
                            # Clue 7: Arnold has the cat
                            if names.index("Arnold") != pets.index("cat"):
                                continue

                            # Clue 5: Ranch is somewhere to the left of Peter
                            if styles.index("ranch") >= names.index("Peter"):
                                continue

                            # Clue 8: Eric is left of Mountain
                            if names.index("Eric") >= vacations.index("mountain"):
                                continue

                            # All constraints satisfied; collect solution
                            solution = {
                                "names": names,
                                "cars": cars,
                                "styles": styles,
                                "pets": pets,
                                "jobs": jobs,
                                "vacations": vacations,
                            }
                            solutions.append(solution)

    # Choose the first solution (should be unique for well-posed puzzle)
    if not solutions:
        raise RuntimeError("No solution found.")
    sol = solutions[0]

    header = ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"]
    rows = []
    for i in range(3):
        rows.append([
            str(i + 1),
            sol["names"][i],
            sol["cars"][i],
            sol["styles"][i],
            sol["pets"][i],
            sol["jobs"][i],
            sol["vacations"][i],
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))