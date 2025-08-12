import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Alice", "Arnold"]
    cars = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names))
    permutations += list(itertools.permutations(cars))
    permutations += list(itertools.permutations(birthdays))
    permutations += list(itertools.permutations(hobbies))

    # Function to check if a given combination satisfies all the clues
    def is_valid_solution(name_perm, car_perm, birthday_perm, hobby_perm):
        # Unpack the permutations into more readable variables
        eric, peter, alice, arnold = name_perm
        tesla, honda, toyota, ford = car_perm
        jan, april, sept, feb = birthday_perm
        painting, cooking, gardening, photography = hobby_perm

        # Check each clue
        if jan == name_perm[1]:  # Clue 1
            return False
        if name_perm.index(photography) >= name_perm.index(eric):  # Clue 2
            return False
        if name_perm.index(photography) >= name_perm.index(peter):  # Clue 3
            return False
        if car_perm.index(honda) + 1 != car_perm.index(tesla):  # Clue 4
            return False
        if abs(car_perm.index(tesla) - hobby_perm.index(gardening)) != 2:  # Clue 5
            return False
        if car_perm.index(tesla) != name_perm.index(arnold):  # Clue 6
            return False
        if birthday_perm.index(feb) != hobby_perm.index(cooking):  # Clue 7
            return False
        if car_perm.index(toyota) != name_perm.index(peter):  # Clue 8
            return False
        if birthday_perm.index(april) != name_perm.index(arnold):  # Clue 9
            return False
        if name_perm.index(alice) != hobby_perm.index(photography):  # Clue 10
            return False
        if birthday_perm.index(jan) != name_perm.index(peter):  # Clue 11
            return False

        return True

    # Iterate over all possible combinations of permutations
    for name_perm in permutations[:24]:
        for car_perm in permutations[24:48]:
            for birthday_perm in permutations[48:72]:
                for hobby_perm in permutations[72:]:
                    if is_valid_solution(name_perm, car_perm, birthday_perm, hobby_perm):
                        # If a valid solution is found, format it as required
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Car", "Birthday", "Hobby"],
                                "rows": []
                            }
                        }
                        for i in range(4):
                            solution["solution"]["rows"].append([
                                str(i + 1),
                                name_perm[i],
                                car_perm[i],
                                birthday_perm[i],
                                hobby_perm[i]
                            ])
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())