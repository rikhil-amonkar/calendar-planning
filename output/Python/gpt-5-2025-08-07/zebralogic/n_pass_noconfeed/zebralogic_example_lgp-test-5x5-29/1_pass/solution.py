import json
from itertools import permutations

def solve():
    houses = list(range(5))  # 0..4 represent houses 1..5
    names = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
    nationalities = ["norwegian", "brit", "swede", "dane", "german"]
    vacations = ["cruise", "mountain", "camping", "beach", "city"]
    educations = ["bachelor", "master", "associate", "doctorate", "high school"]
    occupations = ["artist", "doctor", "engineer", "teacher", "lawyer"]

    # Iterate over all possible assignments of names to houses
    for name_order in permutations(names):
        # Clue 5: Peter is not in the first house.
        if name_order[0] == "Peter":
            continue
        # Clue 13: Bob is not in the fourth house.
        if name_order[3] == "Bob":
            continue

        # Derived from Clue 2 and 17/18 constraints: Arnold cannot be house 1 or 5 (see reasoning)
        arnold_house = name_order.index("Arnold")
        if arnold_house in (0, 4):
            continue

        # Prepare nationality mapping with fixed relations
        nat_template = [None] * 5
        eric_house = name_order.index("Eric")
        peter_house = name_order.index("Peter")
        alice_house = name_order.index("Alice")
        bob_house = name_order.index("Bob")
        arnold_house = name_order.index("Arnold")

        # Clue 12: The person who is an artist is the Swedish person.
        # Clue 6: The person who is an artist is Peter.
        # -> Peter is Swedish.
        nat_template[peter_house] = "swede"
        # Clue 10 and 14: The person who enjoys camping trips is the British person, and is Eric.
        # -> Eric is British.
        nat_template[eric_house] = "brit"
        # Clue 15: Alice is the German.
        nat_template[alice_house] = "german"

        # The remaining nationalities are norwegian and dane for Bob and Arnold
        # Clue 11: The Norwegian and the person with a bachelor's degree (house 3) are next to each other.
        # -> Norwegian must be in house 2 or 4 (index 1 or 3).
        for bob_nat, arnold_nat in [("norwegian", "dane"), ("dane", "norwegian")]:
            nat = nat_template[:]
            nat[bob_house] = bob_nat
            nat[arnold_house] = arnold_nat

            # Ensure uniqueness and completeness of nationalities
            if set(nat) != set(nationalities):
                continue

            # Clue 11 enforcement: Norwegian adjacent to bachelor at house index 2 (house 3)
            norwegian_house = nat.index("norwegian")
            if abs(norwegian_house - 2) != 1:
                continue

            # Education assignments
            edu = [None] * 5
            # Clue 19: The person with a bachelor's degree is in the third house (index 2)
            edu[2] = "bachelor"
            # Clues 7 and 14: Camping person has master, and is Eric.
            # -> Eric has master's degree.
            if eric_house == 2:
                continue  # cannot be bachelor and master simultaneously
            edu[eric_house] = "master"

            # Remaining education values to place: associate, doctorate, high school
            remaining_edu_values = ["associate", "doctorate", "high school"]
            remaining_edu_houses = [i for i in houses if edu[i] is None]

            for edu_perm in permutations(remaining_edu_values):
                edu2 = edu[:]
                for idx, h in enumerate(remaining_edu_houses):
                    edu2[h] = edu_perm[idx]

                # Clue 3: The person with a doctorate is somewhere to the left of Bob.
                if not (edu2.index("doctorate") < bob_house):
                    continue

                # Vacations assignment
                vac = [None] * 5
                # Clue 17: Mountain is in fifth house (index 4).
                vac[4] = "mountain"
                # Clues 7/10/14: Camping is Eric's vacation.
                if vac[eric_house] not in (None, "camping"):
                    continue
                vac[eric_house] = "camping"
                # Clue 4 and 1: Associate degree person likes cruises and is the lawyer.
                assoc_house = edu2.index("associate")
                if vac[assoc_house] not in (None, "cruise"):
                    continue
                vac[assoc_house] = "cruise"
                # Clue 2: Beach directly left of Arnold.
                beach_house = arnold_house - 1
                if beach_house < 0:
                    continue
                if vac[beach_house] not in (None, "beach"):
                    continue
                vac[beach_house] = "beach"
                # Clue 18: Cruise is to the right of beach.
                if not (assoc_house > beach_house):
                    continue

                # Now only city remains unassigned
                remaining_vac_houses = [i for i in houses if vac[i] is None]
                if len(remaining_vac_houses) != 1:
                    continue
                last_vac_house = remaining_vac_houses[0]
                vac[last_vac_house] = "city"
                # Clue 16: Beach is left of city.
                if not (beach_house < last_vac_house):
                    continue

                # Occupations assignment
                occ = [None] * 5
                # Clue 6: The person who is an artist is Peter.
                occ[peter_house] = "artist"
                # Clue 12: The artist is the Swedish person; already satisfied via Peter=Swede.
                if nat[peter_house] != "swede":
                    continue

                # Clue 1: Cruise person is a lawyer. Already set vacc[assoc]=cruise; set occupation there to lawyer.
                if occ[assoc_house] not in (None, "lawyer"):
                    continue
                occ[assoc_house] = "lawyer"

                # Clue 9: Associate's degree is directly left of the engineer.
                eng_house = assoc_house + 1
                if eng_house >= 5:
                    continue
                if occ[eng_house] is not None:
                    continue
                occ[eng_house] = "engineer"

                # Remaining occupations: doctor and teacher
                free_houses = [i for i in houses if occ[i] is None]
                if len(free_houses) != 2:
                    continue

                for roles in permutations(["doctor", "teacher"]):
                    occ2 = occ[:]
                    occ2[free_houses[0]] = roles[0]
                    occ2[free_houses[1]] = roles[1]

                    # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
                    if not (occ2.index("doctor") < nat.index("dane")):
                        continue

                    # All constraints satisfied; build result
                    rows = []
                    for i in range(5):
                        rows.append([
                            str(i + 1),
                            name_order[i],
                            nat[i],
                            vac[i],
                            edu2[i],
                            occ2[i]
                        ])

                    return {
                        "solution": {
                            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                            "rows": rows
                        }
                    }

    raise RuntimeError("No solution found")

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))