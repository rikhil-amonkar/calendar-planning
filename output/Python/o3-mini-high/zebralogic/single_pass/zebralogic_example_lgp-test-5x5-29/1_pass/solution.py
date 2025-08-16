#!/usr/bin/env python3
import json

def is_valid(assignment, complete=False):
    n = len(assignment)
    
    # Constraint C1 & C4: The person who likes cruises must be the lawyer with an associate's degree.
    for house in assignment:
        vac = house.get("Vacation")
        occ = house.get("Occupation")
        edu = house.get("Education")
        if vac == "cruise":
            if occ is not None and occ != "lawyer":
                return False
            if edu is not None and edu != "associate":
                return False
        if occ == "lawyer":
            if vac is not None and vac != "cruise":
                return False
            if edu is not None and edu != "associate":
                return False
        if edu == "associate":
            if vac is not None and vac != "cruise":
                return False
            if occ is not None and occ != "lawyer":
                return False

    # Constraint C2: The person who loves beach vacations is directly left of Arnold.
    for i in range(n - 1):
        left_vac = assignment[i].get("Vacation")
        right_name = assignment[i+1].get("Name")
        if left_vac == "beach":
            if right_name is not None and right_name != "Arnold":
                return False
        if right_name == "Arnold":
            if assignment[i].get("Vacation") is not None and assignment[i].get("Vacation") != "beach":
                return False

    # Constraint C3: The person with a doctorate is somewhere to the left of Bob.
    for i, house in enumerate(assignment):
        if house.get("Name") == "Bob":
            found = False
            for j in range(i):
                if assignment[j].get("Education") == "doctorate":
                    found = True
                    break
            if not found:
                return False

    # Constraint C7, C10 & C14: Camping trips go with master's degree, brit nationality, and must be Eric.
    for house in assignment:
        if house.get("Vacation") == "camping":
            if house.get("Education") is not None and house["Education"] != "master":
                return False
            if house.get("Nationality") is not None and house["Nationality"] != "brit":
                return False
            if house.get("Name") is not None and house["Name"] != "Eric":
                return False
        if house.get("Education") == "master":
            if house.get("Vacation") is not None and house["Vacation"] != "camping":
                return False

    # Constraint C8: The Dane is somewhere to the right of the person who is a doctor (occupation doctor).
    for i, house in enumerate(assignment):
        if house.get("Nationality") == "dane":
            found = False
            for j in range(i):
                if assignment[j].get("Occupation") == "doctor":
                    found = True
                    break
            if not found:
                return False

    # Constraint C9: The person with an associate's degree is directly left of the person who is an engineer.
    for i, house in enumerate(assignment):
        if house.get("Education") == "associate":
            # In a complete assignment, associate cannot be in the last house.
            if i == n - 1:
                if complete:
                    return False
                # In a partial assignment, if it's the last house so far, allow possibility.
            else:
                # If next house is assigned, it must have occupation engineer.
                if assignment[i+1].get("Occupation") is not None:
                    if assignment[i+1].get("Occupation") != "engineer":
                        return False
        if house.get("Occupation") == "engineer":
            if i > 0:
                if assignment[i-1].get("Education") is not None:
                    if assignment[i-1].get("Education") != "associate":
                        return False

    # Constraint C11: The Norwegian and the person with a bachelor's degree are next to each other.
    # Clue C19 forces bachelor's to be in the third house (index 2). Check neighbors only if both exist.
    if n >= 4 and assignment[2].get("Education") == "bachelor":
        # When both neighbors of house index 2 are assigned (i.e. houses index 1 and 3 exist)
        if 1 < n and 3 < n:
            if (assignment[1].get("Nationality") is not None and assignment[3].get("Nationality") is not None):
                if assignment[1]["Nationality"] != "norwegian" and assignment[3]["Nationality"] != "norwegian":
                    return False

    # Constraint C12: The person who is an artist is Peter and is swede.
    for house in assignment:
        if house.get("Occupation") == "artist":
            if house.get("Name") is not None and house["Name"] != "Peter":
                return False
            if house.get("Nationality") is not None and house["Nationality"] != "swede":
                return False
        if house.get("Name") == "Peter":
            if house.get("Occupation") is not None and house["Occupation"] != "artist":
                return False
            if house.get("Nationality") is not None and house["Nationality"] != "swede":
                return False

    # Constraint C15: Alice is the German.
    for house in assignment:
        if house.get("Name") == "Alice":
            if house.get("Nationality") is not None and house["Nationality"] != "german":
                return False

    # Constraint C16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
    idx_beach = None
    idx_city = None
    for i, house in enumerate(assignment):
        if house.get("Vacation") == "beach":
            if idx_beach is None:
                idx_beach = i
        if house.get("Vacation") == "city":
            if idx_city is None:
                idx_city = i
    if idx_beach is not None and idx_city is not None:
        if idx_beach >= idx_city:
            return False

    # Constraint C18: The person who likes cruises is somewhere to the right of the person who loves beach vacations.
    idx_cruise = None
    idx_beach = None
    for i, house in enumerate(assignment):
        if house.get("Vacation") == "cruise":
            if idx_cruise is None:
                idx_cruise = i
        if house.get("Vacation") == "beach":
            if idx_beach is None:
                idx_beach = i
    if idx_cruise is not None and idx_beach is not None:
        if idx_cruise <= idx_beach:
            return False

    # Constraint C19: The person with a bachelor's degree is in the third house (index 2).
    if n >= 3:
        if assignment[2].get("Education") is not None and assignment[2]["Education"] != "bachelor":
            return False

    return True

def solve():
    names = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
    nationalities = ["norwegian", "brit", "swede", "dane", "german"]
    vacations = ["cruise", "mountain", "camping", "beach", "city"]
    educations = ["bachelor", "master", "associate", "doctorate", "high school"]
    occupations = ["artist", "doctor", "engineer", "teacher", "lawyer"]

    solutions = []
    
    def backtrack(assignment, rem_names, rem_nats, rem_vacs, rem_edus, rem_occs):
        i = len(assignment)
        if i == 5:
            if is_valid(assignment, complete=True):
                solutions.append([house.copy() for house in assignment])
            return
        
        for name in rem_names:
            # Clue 5: Peter is not in the first house.
            if i == 0 and name == "Peter":
                continue
            # Clue 13: Bob is not in the fourth house (index 3).
            if i == 3 and name == "Bob":
                continue
            
            for nat in rem_nats:
                # Clue 15: Alice is the German.
                if name == "Alice" and nat != "german":
                    continue
                # Clue 12 & 6: Peter must be swede and artist.
                if name == "Peter" and nat != "swede":
                    continue
                
                for vac in rem_vacs:
                    # Clue 17: The person who enjoys mountain retreats is in the fifth house.
                    if i == 4 and vac != "mountain":
                        continue
                        
                    for edu in rem_edus:
                        # Clue 19: Bachelor's degree is in the third house (index 2).
                        if i == 2 and edu != "bachelor":
                            continue
                        # If education is associate, it cannot be in the last house
                        if edu == "associate" and i == 4:
                            continue
                        
                        for occ in rem_occs:
                            # Clue 14: The person who enjoys camping trips is Eric.
                            if vac == "camping" and name != "Eric":
                                continue
                            # Clue 7: Camping trips go with master's degree.
                            if vac == "camping" and edu != "master":
                                continue
                            # Clue 10: Camping trips go with brit nationality.
                            if vac == "camping" and nat != "brit":
                                continue
                            # Clue 1 & 4: Cruise must go with lawyer and associate.
                            if vac == "cruise" and (occ != "lawyer" or edu != "associate"):
                                continue
                            if occ == "lawyer" and (vac != "cruise" or edu != "associate"):
                                continue
                            if edu == "associate" and (vac != "cruise" or occ != "lawyer"):
                                continue
                            # Clue 6 & 12: Peter is the artist.
                            if name == "Peter" and occ != "artist":
                                continue
                            if occ == "artist" and name != "Peter":
                                continue
                            
                            house = {
                                "Name": name,
                                "Nationality": nat,
                                "Vacation": vac,
                                "Education": edu,
                                "Occupation": occ
                            }
                            new_assignment = assignment + [house]
                            if not is_valid(new_assignment, complete=False):
                                continue
                            
                            new_rem_names = rem_names.copy()
                            new_rem_names.remove(name)
                            new_rem_nats = rem_nats.copy()
                            new_rem_nats.remove(nat)
                            new_rem_vacs = rem_vacs.copy()
                            new_rem_vacs.remove(vac)
                            new_rem_edus = rem_edus.copy()
                            new_rem_edus.remove(edu)
                            new_rem_occs = rem_occs.copy()
                            new_rem_occs.remove(occ)
                            
                            backtrack(new_assignment, new_rem_names, new_rem_nats, new_rem_vacs, new_rem_edus, new_rem_occs)
                            
    backtrack([], names, nationalities, vacations, educations, occupations)
    return solutions

def main():
    sols = solve()
    if sols:
        sol = sols[0]
        result = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": []
            }
        }
        for i, house in enumerate(sol):
            row = [
                str(i+1),
                house["Name"],
                house["Nationality"],
                house["Vacation"],
                house["Education"],
                house["Occupation"]
            ]
            result["solution"]["rows"].append(row)
        print(json.dumps(result))
        
if __name__ == "__main__":
    main()