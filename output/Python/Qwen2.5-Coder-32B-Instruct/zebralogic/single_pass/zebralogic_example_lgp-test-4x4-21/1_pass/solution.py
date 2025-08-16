import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Eric", "Peter", "Alice", "Arnold"]
    cars = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(names))
    car_permutations = list(itertools.permutations(cars))
    birthday_permutations = list(itertools.permutations(birthdays))
    hobby_permutations = list(itertools.permutations(hobbies))

    for name_order in permutations:
        for car_order in car_permutations:
            for birthday_order in birthday_permutations:
                for hobby_order in hobby_permutations:
                    # Create a dictionary to map attributes to houses
                    house_attributes = {house: {} for house in houses}
                    for i, house in enumerate(houses):
                        house_attributes[house]["Name"] = name_order[i]
                        house_attributes[house]["CarModel"] = car_order[i]
                        house_attributes[house]["Birthday"] = birthday_order[i]
                        house_attributes[house]["Hobby"] = hobby_order[i]

                    # Check all constraints
                    if (house_attributes[1]["Birthday"] != "jan" and  # Constraint 1
                        house_attributes[2]["Birthday"] != "jan" and
                        house_attributes[3]["Birthday"] != "jan" and
                        house_attributes[4]["Birthday"] != "jan" and
                        (house_attributes[1]["Hobby"] == "photography" or  # Constraint 2
                         house_attributes[2]["Hobby"] == "photography" and house_attributes[3]["Name"] != "Eric" or
                         house_attributes[3]["Hobby"] == "photography" and house_attributes[4]["Name"] != "Eric") and
                        (house_attributes[1]["Hobby"] == "photography" or  # Constraint 3
                         house_attributes[2]["Hobby"] == "photography" and house_attributes[3]["Name"] != "Peter" or
                         house_attributes[3]["Hobby"] == "photography" and house_attributes[4]["Name"] != "Peter") and
                        (car_order.index("honda civic") + 1 == car_order.index("tesla model 3")) and  # Constraint 4
                        (abs(car_order.index("tesla model 3") - hobby_order.index("gardening")) == 2) and  # Constraint 5
                        (name_order[car_order.index("tesla model 3")] == "Arnold") and  # Constraint 6
                        (birthday_order[name_order.index("Peter")] == "jan") and  # Constraint 11
                        (birthday_order[hobby_order.index("cooking")] == "feb") and  # Constraint 7
                        (name_order[car_order.index("toyota camry")] == "Peter") and  # Constraint 8
                        (birthday_order[name_order.index("Arnold")] == "april") and  # Constraint 9
                        (hobby_order[name_order.index("Alice")] == "photography")):  # Constraint 10

                        # If all constraints are satisfied, format the solution
                        solution_rows = []
                        for house in houses:
                            row = [str(house)]
                            for attr in ["Name", "CarModel", "Birthday", "Hobby"]:
                                row.append(house_attributes[house][attr])
                            solution_rows.append(row)

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                                "rows": solution_rows
                            }
                        }

                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())