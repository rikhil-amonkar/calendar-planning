#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Arnold", "Peter", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    educations = ["associate", "high school", "bachelor"]
    smoothies = ["desert", "cherry", "watermelon"]
    hobbies = ["gardening", "cooking", "photography"]

    solution = None
    # Generate all possible assignments using permutations
    for perm_names in itertools.permutations(names):
        for perm_occ in itertools.permutations(occupations):
            for perm_edu in itertools.permutations(educations):
                for perm_sm in itertools.permutations(smoothies):
                    for perm_hobby in itertools.permutations(hobbies):
                        houses = []
                        for i in range(3):
                            houses.append({
                                "Name": perm_names[i],
                                "Occupation": perm_occ[i],
                                "Education": perm_edu[i],
                                "Smoothie": perm_sm[i],
                                "Hobby": perm_hobby[i]
                            })
                        # Constraint 2: Arnold is not in the third house.
                        if houses[2]["Name"] == "Arnold":
                            continue

                        # Constraint 4: The person who loves cooking is in the second house.
                        if houses[1]["Hobby"] != "cooking":
                            continue

                        # Constraint 5: The person who loves cooking is Peter.
                        if houses[1]["Name"] != "Peter":
                            continue

                        # Constraint 1: The Desert smoothie lover is the person who is a doctor.
                        valid = True
                        for house in houses:
                            if house["Occupation"] == "doctor" and house["Smoothie"] != "desert":
                                valid = False
                                break
                            if house["Smoothie"] == "desert" and house["Occupation"] != "doctor":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
                        try:
                            index_peter = next(i for i, house in enumerate(houses) if house["Name"] == "Peter")
                            index_cherry = next(i for i, house in enumerate(houses) if house["Smoothie"] == "cherry")
                        except StopIteration:
                            continue
                        if index_cherry <= index_peter:
                            continue

                        # Constraint 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        try:
                            index_associate = next(i for i, house in enumerate(houses) if house["Education"] == "associate")
                            index_gardening = next(i for i, house in enumerate(houses) if house["Hobby"] == "gardening")
                        except StopIteration:
                            continue
                        if index_associate <= index_gardening:
                            continue

                        # Constraint 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        try:
                            index_bachelor = next(i for i, house in enumerate(houses) if house["Education"] == "bachelor")
                            index_desert = next(i for i, house in enumerate(houses) if house["Smoothie"] == "desert")
                        except StopIteration:
                            continue
                        if index_bachelor <= index_desert:
                            continue

                        # Constraint 8: The person who loves cooking is the person who is a doctor.
                        try:
                            index_cooking = next(i for i, house in enumerate(houses) if house["Hobby"] == "cooking")
                        except StopIteration:
                            continue
                        if houses[index_cooking]["Occupation"] != "doctor":
                            continue

                        # Constraint 9: The photography enthusiast is the person who is a teacher.
                        valid = True
                        for house in houses:
                            if house["Hobby"] == "photography" and house["Occupation"] != "teacher":
                                valid = False
                                break
                            if house["Occupation"] == "teacher" and house["Hobby"] != "photography":
                                valid = False
                                break
                        if not valid:
                            continue

                        # All constraints satisfied; record the solution.
                        solution = houses
                        break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    # Prepare the output structure.
    header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
    rows = []
    if solution is not None:
        for i, house in enumerate(solution):
            rows.append([
                str(i + 1),
                house["Name"],
                house["Occupation"],
                house["Education"],
                house["Smoothie"],
                house["Hobby"]
            ])
    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()