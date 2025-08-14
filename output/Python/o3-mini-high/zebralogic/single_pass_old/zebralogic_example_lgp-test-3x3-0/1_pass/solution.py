#!/usr/bin/env python3
import json
import itertools

def main():
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    solution = None

    # Iterate over all possible assignments (permutations) for each attribute
    for name_perm in itertools.permutations(names):
        for edu_perm in itertools.permutations(educations):
            for occ_perm in itertools.permutations(occupations):
                houses = []
                for i in range(3):
                    house = {
                        "House": str(i+1),
                        "Name": name_perm[i],
                        "Education": edu_perm[i],
                        "Occupation": occ_perm[i]
                    }
                    houses.append(house)

                valid = True

                # Clue 3: Peter is the person with a high school diploma.
                for house in houses:
                    if house["Name"] == "Peter" and house["Education"] != "high school":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
                teacher_index = None
                for i in range(3):
                    if houses[i]["Occupation"] == "teacher":
                        teacher_index = i
                        break
                # Teacher cannot be in the rightmost house if a neighbor to the right is required.
                if teacher_index is None or teacher_index == 2:
                    continue
                if houses[teacher_index + 1]["Education"] != "associate":
                    continue

                # Clue 2: The person with an associate's degree and Eric are next to each other.
                associate_index = None
                eric_index = None
                for i in range(3):
                    if houses[i]["Education"] == "associate":
                        associate_index = i
                    if houses[i]["Name"] == "Eric":
                        eric_index = i
                if associate_index is None or eric_index is None or abs(associate_index - eric_index) != 1:
                    continue

                # Clue 4: The person who is a doctor is the person with a bachelor's degree.
                doctor_index = None
                for i in range(3):
                    if houses[i]["Occupation"] == "doctor":
                        doctor_index = i
                        break
                if doctor_index is None or houses[doctor_index]["Education"] != "bachelor":
                    continue

                solution = houses
                break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": [
                [house["House"], house["Name"], house["Education"], house["Occupation"]]
                for house in solution
            ]
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()