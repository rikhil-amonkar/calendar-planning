#!/usr/bin/env python3
import json

def check_constraints(houses, avail):
    n = len(houses)
    # Check local, house-specific constraints:
    for i, house in enumerate(houses):
        name = house["Name"]
        nat = house["Nationality"]
        vac = house["Vacation"]
        edu = house["Education"]
        occ = house["Occupation"]
        
        # Clue 5: Peter is not in the first house.
        if i == 0 and name == "Peter":
            return False
        # Clue 19: The person with a bachelor's degree is in the third house.
        if i == 2 and edu != "bachelor":
            return False
        # Clue 17: The person who enjoys mountain retreats is in the fifth house.
        if i == 4 and vac != "mountain":
            return False
        # Clue 13: Bob is not in the fourth house.
        if i == 3 and name == "Bob":
            return False
        # Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
        # (Since bachelor's is fixed in house 3 (index 2), Norwegian must be in house 2 or 4 (indexes 1 or 3)).
        if nat == "norwegian" and i not in [1, 3]:
            return False
        # Clue 15: Alice is the German.
        if name == "Alice" and nat != "german":
            return False
        # Clues 14 & 7 & 10: The person who enjoys camping trips is Eric, has a master's degree and is British.
        if name == "Eric":
            if vac != "camping" or edu != "master" or nat != "brit":
                return False
        if vac == "camping":
            if name != "Eric" or edu != "master" or nat != "brit":
                return False
        if edu == "master":
            if vac != "camping":
                return False
        # Clues 1 & 4: The person who likes going on cruises is the person who is a lawyer and has an associate's degree.
        if vac == "cruise":
            if edu != "associate" or occ != "lawyer":
                return False
        if edu == "associate":
            if vac != "cruise":
                return False
        if occ == "lawyer":
            if vac != "cruise":
                return False
        # Clues 6 & 12: The person who is an artist is Peter and is Swedish.
        if occ == "artist":
            if name != "Peter" or nat != "swede":
                return False
        if name == "Peter":
            if occ != "artist":
                return False
        # Clue 2: The person who loves beach vacations is directly left of Arnold.
        if vac == "beach":
            # A house with beach cannot be the last house.
            if i == 4:
                return False
            if i < n - 1:
                if houses[i+1]["Name"] != "Arnold":
                    return False
            else:
                # if neighbor not yet assigned, ensure that "Arnold" is still available.
                if n < 5 and "Arnold" not in avail["Name"]:
                    return False
        if name == "Arnold":
            # Arnold cannot be in the first house and must have a left neighbor with beach.
            if i == 0:
                return False
            else:
                if houses[i-1]["Vacation"] != "beach":
                    return False
        # Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
        if vac == "city":
            found_beach = False
            for j in range(i):
                if houses[j]["Vacation"] == "beach":
                    found_beach = True
                    break
            if not found_beach:
                return False

        # Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
        if vac == "cruise":
            found_beach = False
            for j in range(i):
                if houses[j]["Vacation"] == "beach":
                    found_beach = True
                    break
            if not found_beach:
                return False

    # Cross-house (ordering) constraints:
    # Clue 3: The person with a doctorate is somewhere to the left of Bob.
    for i, house in enumerate(houses):
        if house["Name"] == "Bob":
            if i == 0:
                return False
            found_doc = False
            for j in range(i):
                if houses[j]["Education"] == "doctorate":
                    found_doc = True
                    break
            if not found_doc:
                return False

    # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
    for i, house in enumerate(houses):
        if house["Nationality"] == "dane":
            found_doctor = False
            for j in range(i):
                if houses[j]["Occupation"] == "doctor":
                    found_doctor = True
                    break
            if not found_doctor:
                return False

    # Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
    for i in range(len(houses) - 1):
        if houses[i]["Education"] == "associate":
            if houses[i+1]["Occupation"] != "engineer":
                return False
        if houses[i+1]["Occupation"] == "engineer":
            if houses[i]["Education"] != "associate":
                return False
    # Forward–checking for associate–engineer relation:
    if n < 5 and n > 0:
        if houses[-1]["Education"] == "associate":
            if "engineer" not in avail["Occupation"]:
                return False

    # Clue 11 (Norwegian next to bachelor) final check when all houses assigned.
    if len(houses) == 5:
        # Bachelor is in house 3 (index 2), so Norwegian must be in house 2 or 4 (indexes 1 or 3).
        if not (houses[1]["Nationality"] == "norwegian" or houses[3]["Nationality"] == "norwegian"):
            return False

    return True

def backtrack(index, houses, avail):
    if index == 5:
        if check_constraints(houses, avail):
            return houses
        else:
            return None

    names = avail["Name"]
    nats = avail["Nationality"]
    vacs = avail["Vacation"]
    edus = avail["Education"]
    occs = avail["Occupation"]

    for name in names:
        for nat in nats:
            for vac in vacs:
                for edu in edus:
                    for occ in occs:
                        # Enforce fixed positions:
                        # House 3 (index 2) must have bachelor's degree.
                        if index == 2 and edu != "bachelor":
                            continue
                        # House 5 (index 4) must have mountain vacation.
                        if index == 4 and vac != "mountain":
                            continue
                        # Also, a house with beach vacation cannot be the fifth house.
                        if vac == "beach" and index == 4:
                            continue

                        house = {
                            "Name": name,
                            "Nationality": nat,
                            "Vacation": vac,
                            "Education": edu,
                            "Occupation": occ
                        }
                        new_avail = {
                            "Name": [x for x in avail["Name"] if x != name],
                            "Nationality": [x for x in avail["Nationality"] if x != nat],
                            "Vacation": [x for x in avail["Vacation"] if x != vac],
                            "Education": [x for x in avail["Education"] if x != edu],
                            "Occupation": [x for x in avail["Occupation"] if x != occ]
                        }
                        new_houses = houses + [house]
                        if not check_constraints(new_houses, new_avail):
                            continue
                        result = backtrack(index + 1, new_houses, new_avail)
                        if result is not None:
                            return result
    return None

def main():
    avail = {
        "Name": ["Eric", "Peter", "Alice", "Bob", "Arnold"],
        "Nationality": ["norwegian", "brit", "swede", "dane", "german"],
        "Vacation": ["cruise", "mountain", "camping", "beach", "city"],
        "Education": ["bachelor", "master", "associate", "doctorate", "high school"],
        "Occupation": ["artist", "doctor", "engineer", "teacher", "lawyer"]
    }
    solution = backtrack(0, [], avail)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"], "rows": []}}
    else:
        rows = []
        for i, house in enumerate(solution):
            row = [str(i+1), house["Name"], house["Nationality"], house["Vacation"], house["Education"], house["Occupation"]]
            rows.append(row)
        output = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": rows
            }
        }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()