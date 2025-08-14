#!/usr/bin/env python3
import json
from itertools import permutations

def main():
    names_list = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
    nationality_list = ["norwegian", "brit", "swede", "dane", "german"]
    vacation_list = ["cruise", "mountain", "camping", "beach", "city"]
    education_list = ["bachelor", "master", "associate", "doctorate", "high school"]
    occupation_list = ["artist", "doctor", "engineer", "teacher", "lawyer"]

    # Pre-filter education: bachelor's degree must be in the third house (index 2)
    edu_perms = [edu for edu in permutations(education_list) if edu[2] == "bachelor"]
    # Pre-filter vacation: mountain vacation must be in the fifth house (index 4)
    vac_perms = [vac for vac in permutations(vacation_list) if vac[4] == "mountain"]

    for edu in edu_perms:
        for vac in vac_perms:
            try:
                camping_index = vac.index("camping")
                beach_index = vac.index("beach")
                city_index = vac.index("city")
                cruise_index = vac.index("cruise")
            except ValueError:
                continue

            # Clue 7: The camping person has a master's degree.
            if edu[camping_index] != "master":
                continue
            # Clue 4: Associate's degree <-> Cruise vacation.
            valid_associate = True
            for i in range(5):
                if edu[i] == "associate" and vac[i] != "cruise":
                    valid_associate = False
                    break
                if vac[i] == "cruise" and edu[i] != "associate":
                    valid_associate = False
                    break
            if not valid_associate:
                continue
            # Clue 16: The beach lover is somewhere to the left of the city break lover.
            if beach_index >= city_index:
                continue
            # Clue 18: The cruise lover is somewhere to the right of the beach lover.
            if beach_index >= cruise_index:
                continue

            for names in permutations(names_list):
                # Clue 5: Peter is not in the first house.
                if names[0] == "Peter":
                    continue
                # Clue 13: Bob is not in the fourth house.
                if names[3] == "Bob":
                    continue
                # Clue 14: The camping person is Eric.
                if names[camping_index] != "Eric":
                    continue
                # Clue 2: The beach lover is directly left of Arnold.
                idx_arnold = names.index("Arnold")
                if idx_arnold == 0:
                    continue
                if vac[idx_arnold - 1] != "beach":
                    continue
                # Clue 3: The doctorate holder is somewhere to the left of Bob.
                if edu.index("doctorate") >= names.index("Bob"):
                    continue

                for nat in permutations(nationality_list):
                    # Clue 15: Alice is the German.
                    if nat[names.index("Alice")] != "german":
                        continue
                    # Clue 10: The camping person is the British person.
                    if nat[camping_index] != "brit":
                        continue
                    # Clue 11: The Norwegian and the bachelor's holder (in house 3) are next to each other.
                    if not (nat[1] == "norwegian" or nat[3] == "norwegian"):
                        continue
                    # Clue 12: The artist is the Swedish person.
                    # Since Clue 6 forces Peter to be the artist, Peter must be Swedish.
                    if nat[names.index("Peter")] != "swede":
                        continue

                    for occ in permutations(occupation_list):
                        # Clue 1: Cruise lover is the lawyer.
                        valid_occ = True
                        for i in range(5):
                            if vac[i] == "cruise" and occ[i] != "lawyer":
                                valid_occ = False
                                break
                            if occ[i] == "lawyer" and vac[i] != "cruise":
                                valid_occ = False
                                break
                        if not valid_occ:
                            continue
                        # Clue 6: The artist is Peter.
                        if occ[names.index("Peter")] != "artist":
                            continue
                        # Clue 9: The associate-degree holder is directly left of the engineer.
                        found_pair = False
                        for i in range(4):
                            if edu[i] == "associate" and occ[i+1] == "engineer":
                                found_pair = True
                                break
                        if not found_pair:
                            continue
                        # Clue 8: The Dane is somewhere to the right of the doctor.
                        if occ.index("doctor") >= nat.index("dane"):
                            continue

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "nationality", "vacation", "education", "occupation"],
                                "rows": []
                            }
                        }
                        for i in range(5):
                            solution["solution"]["rows"].append([
                                str(i+1),
                                names[i],
                                nat[i],
                                vac[i],
                                edu[i],
                                occ[i]
                            ])
                        print(json.dumps(solution))
                        return

if __name__ == "__main__":
    main()