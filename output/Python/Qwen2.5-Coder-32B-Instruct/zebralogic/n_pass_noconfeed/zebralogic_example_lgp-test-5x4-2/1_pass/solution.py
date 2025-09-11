import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    colors = ["blue", "green", "white", "yellow", "red"]
    phones = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for color_perm in itertools.permutations(colors):
            for phone_perm in itertools.permutations(phones):
                for occupation_perm in itertools.permutations(occupations):
                    # Unpack permutations
                    bob_house = name_perm.index("Bob") + 1
                    arnold_house = name_perm.index("Arnold") + 1
                    alice_house = name_perm.index("Alice") + 1
                    eric_house = name_perm.index("Eric") + 1
                    peter_house = name_perm.index("Peter") + 1

                    doctor_house = occupation_perm.index("doctor") + 1
                    lawyer_house = occupation_perm.index("lawyer") + 1
                    engineer_house = occupation_perm.index("engineer") + 1
                    teacher_house = occupation_perm.index("teacher") + 1
                    artist_house = occupation_perm.index("artist") + 1

                    blue_house = color_perm.index("blue") + 1
                    green_house = color_perm.index("green") + 1
                    white_house = color_perm.index("white") + 1
                    yellow_house = color_perm.index("yellow") + 1
                    red_house = color_perm.index("red") + 1

                    huawei_house = phone_perm.index("huawei p50") + 1
                    samsung_house = phone_perm.index("samsung galaxy s21") + 1
                    oneplus_house = phone_perm.index("oneplus 9") + 1
                    iphone_house = phone_perm.index("iphone 13") + 1
                    google_house = phone_perm.index("google pixel 6") + 1

                    # Check all constraints
                    if (engineer_house > lawyer_house and
                        bob_house == 2 and
                        doctor_house == samsung_house and
                        doctor_house == blue_house and
                        green_house != 5 and
                        lawyer_house == oneplus_house and
                        blue_house + 1 == red_house and
                        lawyer_house > samsung_house and
                        abs(google_house - huawei_house) == 2 and
                        arnold_house == engineer_house and
                        alice_house == yellow_house and
                        eric_house == google_house and
                        google_house == teacher_house and
                        red_house > teacher_house):

                        # Construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                                "rows": []
                            }
                        }

                        for house in houses:
                            name = name_perm[house - 1]
                            color = color_perm[house - 1]
                            phone = phone_perm[house - 1]
                            occupation = occupation_perm[house - 1]
                            solution["solution"]["rows"].append([str(house), name, color, phone, occupation])

                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())