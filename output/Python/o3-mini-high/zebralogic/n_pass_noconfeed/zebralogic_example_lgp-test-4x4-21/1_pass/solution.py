import itertools
import json
import sys

def main():
    houses = ["1", "2", "3", "4"]
    names_list = ["Eric", "Peter", "Alice", "Arnold"]
    car_models_list = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays_list = ["jan", "april", "sept", "feb"]
    hobbies_list = ["painting", "cooking", "gardening", "photography"]

    for p_names in itertools.permutations(names_list):
        for p_cars in itertools.permutations(car_models_list):
            # Constraint 4: Honda Civic must be directly left of Tesla Model 3.
            try:
                idx_tesla = p_cars.index("tesla model 3")
            except ValueError:
                continue
            if idx_tesla == 0 or p_cars[idx_tesla - 1] != "honda civic":
                continue

            for p_birthdays in itertools.permutations(birthdays_list):
                # Constraint 1: The person whose birthday is in January is not in the second house.
                if p_birthdays[1] == "jan":
                    continue

                for p_hobbies in itertools.permutations(hobbies_list):
                    # Constraint 10: Alice is the photography enthusiast.
                    if p_hobbies[p_names.index("Alice")] != "photography":
                        continue

                    # Constraint 2: The photography enthusiast is somewhere to the left of Eric.
                    # Constraint 3: The photography enthusiast is somewhere to the left of Peter.
                    idx_photo = p_hobbies.index("photography")
                    if idx_photo >= p_names.index("Eric"):
                        continue
                    if idx_photo >= p_names.index("Peter"):
                        continue

                    # Constraint 7: The person whose birthday is in February is the person who loves cooking.
                    if p_hobbies[p_birthdays.index("feb")] != "cooking":
                        continue

                    # Constraint 8: The person who owns a Toyota Camry is Peter.
                    if p_names[p_cars.index("toyota camry")] != "Peter":
                        continue

                    # Constraint 9: The person whose birthday is in April is Arnold.
                    if p_names[p_birthdays.index("april")] != "Arnold":
                        continue

                    # Constraint 11: Peter is the person whose birthday is in January.
                    if p_birthdays[p_names.index("Peter")] != "jan":
                        continue

                    # Constraint 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
                    idx_gardening = p_hobbies.index("gardening")
                    if abs(idx_tesla - idx_gardening) != 2:
                        continue

                    # Constraint 6: The person who owns a Tesla Model 3 is Arnold.
                    if p_names[idx_tesla] != "Arnold":
                        continue

                    # If all constraints are satisfied, compile the solution.
                    solution_rows = []
                    for i in range(4):
                        solution_rows.append([
                            houses[i],
                            p_names[i],
                            p_cars[i],
                            p_birthdays[i],
                            p_hobbies[i]
                        ])

                    solution = {
                        "solution": {
                            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(solution))
                    sys.exit(0)

if __name__ == "__main__":
    main()