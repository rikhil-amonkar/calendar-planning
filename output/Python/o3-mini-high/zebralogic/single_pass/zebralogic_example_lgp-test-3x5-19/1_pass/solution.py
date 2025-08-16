#!/usr/bin/env python3
import itertools
import json

def main():
    houses = [1, 2, 3]
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']

    solution = None

    # Iterate over all permutations for each attribute
    for perm_names in itertools.permutations(names):
        for perm_occ in itertools.permutations(occupations):
            for perm_edu in itertools.permutations(educations):
                for perm_smoo in itertools.permutations(smoothies):
                    for perm_hobby in itertools.permutations(hobbies):
                        candidate = []
                        for i in range(3):
                            candidate.append({
                                "House": i + 1,
                                "Name": perm_names[i],
                                "Occupation": perm_occ[i],
                                "Education": perm_edu[i],
                                "Smoothie": perm_smoo[i],
                                "Hobby": perm_hobby[i]
                            })
                        
                        valid = True
                        
                        # Clue 1: The Desert smoothie lover is the person who is a doctor.
                        for house in candidate:
                            if house["Smoothie"] == "desert" and house["Occupation"] != "doctor":
                                valid = False
                                break
                            if house["Occupation"] == "doctor" and house["Smoothie"] != "desert":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 2: Arnold is not in the third house.
                        if candidate[2]["Name"] == "Arnold":
                            continue

                        # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
                        index_peter = None
                        index_cherry = None
                        for i, house in enumerate(candidate):
                            if house["Name"] == "Peter":
                                index_peter = i
                            if house["Smoothie"] == "cherry":
                                index_cherry = i
                        if index_peter is None or index_cherry is None or index_cherry <= index_peter:
                            continue

                        # Clue 4: The person who loves cooking is in the second house.
                        if candidate[1]["Hobby"] != "cooking":
                            continue

                        # Clue 5: The person who loves cooking is Peter.
                        if candidate[1]["Name"] != "Peter":
                            continue

                        # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        index_associate = None
                        index_gardening = None
                        for i, house in enumerate(candidate):
                            if house["Education"] == "associate":
                                index_associate = i
                            if house["Hobby"] == "gardening":
                                index_gardening = i
                        if index_associate is None or index_gardening is None or index_associate <= index_gardening:
                            continue

                        # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        index_bachelor = None
                        index_desert = None
                        for i, house in enumerate(candidate):
                            if house["Education"] == "bachelor":
                                index_bachelor = i
                            if house["Smoothie"] == "desert":
                                index_desert = i
                        if index_bachelor is None or index_desert is None or index_bachelor <= index_desert:
                            continue

                        # Clue 8: The person who loves cooking is the person who is a doctor.
                        for house in candidate:
                            if house["Hobby"] == "cooking" and house["Occupation"] != "doctor":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 9: The photography enthusiast is the person who is a teacher.
                        for house in candidate:
                            if house["Hobby"] == "photography" and house["Occupation"] != "teacher":
                                valid = False
                                break
                        if not valid:
                            continue

                        solution = candidate
                        break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    # Prepare the output in the required JSON format.
    header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
    rows = []
    if solution:
        # Ensure the solution is sorted by house number.
        solution.sort(key=lambda x: x["House"])
        for house in solution:
            rows.append([
                str(house["House"]),
                house["Name"],
                house["Occupation"],
                house["Education"],
                house["Smoothie"],
                house["Hobby"]
            ])
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()