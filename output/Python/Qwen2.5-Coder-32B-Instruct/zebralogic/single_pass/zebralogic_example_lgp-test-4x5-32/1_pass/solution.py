import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthdays = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for birthday_perm in itertools.permutations(birthdays):
                for education_perm in itertools.permutations(educations):
                    for smoothie_perm in itertools.permutations(smoothies):
                        # Create a list of dictionaries for each house
                        assignments = [
                            {"house": 1, "name": name_perm[0], "hobby": hobby_perm[0], "birthday": birthday_perm[0], "education": education_perm[0], "smoothie": smoothie_perm[0]},
                            {"house": 2, "name": name_perm[1], "hobby": hobby_perm[1], "birthday": birthday_perm[1], "education": education_perm[1], "smoothie": smoothie_perm[1]},
                            {"house": 3, "name": name_perm[2], "hobby": hobby_perm[2], "birthday": birthday_perm[2], "education": education_perm[2], "smoothie": smoothie_perm[2]},
                            {"house": 4, "name": name_perm[3], "hobby": hobby_perm[3], "birthday": birthday_perm[3], "education": education_perm[3], "smoothie": smoothie_perm[3]}
                        ]

                        # Check constraints
                        if (
                            # 1. The Desert smoothie lover is the person whose birthday is in January.
                            any(person["smoothie"] == "desert" and person["birthday"] == "jan" for person in assignments) and
                            # 2. Eric is the person with a bachelor's degree.
                            any(person["name"] == "Eric" and person["education"] == "bachelor" for person in assignments) and
                            # 3. The person whose birthday is in January is the person with a bachelor's degree.
                            any(person["birthday"] == "jan" and person["education"] == "bachelor" for person in assignments) and
                            # 4. The person with a high school diploma is in the third house.
                            assignments[2]["education"] == "high school" and
                            # 5. The Watermelon smoothie lover is not in the third house.
                            assignments[2]["smoothie"] != "watermelon" and
                            # 6. The person with an associate's degree is Arnold.
                            any(person["name"] == "Arnold" and person["education"] == "associate" for person in assignments) and
                            # 7. The person with a master's degree is the person who paints as a hobby.
                            any(person["education"] == "master" and person["hobby"] == "painting" for person in assignments) and
                            # 8. There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
                            abs(next(i for i, person in enumerate(assignments) if person["smoothie"] == "dragonfruit") -
                                next(i for i, person in enumerate(assignments) if person["birthday"] == "sept")) == 2 and
                            # 9. The person with a high school diploma is the person whose birthday is in September.
                            any(person["education"] == "high school" and person["birthday"] == "sept" for person in assignments) and
                            # 10. The person who loves cooking is Alice.
                            any(person["name"] == "Alice" and person["hobby"] == "cooking" for person in assignments) and
                            # 11. The person whose birthday is in April and the person who enjoys gardening are next to each other.
                            abs(next(i for i, person in enumerate(assignments) if person["birthday"] == "april") -
                                next(i for i, person in enumerate(assignments) if person["hobby"] == "gardening")) == 1 and
                            # 12. The person who paints as a hobby is the person whose birthday is in February.
                            any(person["hobby"] == "painting" and person["birthday"] == "feb" for person in assignments)
                        ):
                            # If all constraints are satisfied, format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                                    "rows": [[str(person["house"]), person["name"], person["hobby"], person["birthday"], person["education"], person["smoothie"]] for person in assignments]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())