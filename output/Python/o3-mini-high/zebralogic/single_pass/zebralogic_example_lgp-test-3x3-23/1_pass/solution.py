#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # Define the attributes for the houses
    houses = [1, 2, 3]  # House numbers (left-to-right)
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    # Iterate over all possible assignments of names, occupations, and hobbies to the houses.
    for perm_names in itertools.permutations(names):
        for perm_occs in itertools.permutations(occupations):
            for perm_hobbies in itertools.permutations(hobbies):
                # Build the candidate solution for houses in order (house 1 is index 0, etc.)
                candidate = []
                for i in range(3):
                    candidate.append({
                        "House": houses[i],
                        "Name": perm_names[i],
                        "Occupation": perm_occs[i],
                        "Hobby": perm_hobbies[i]
                    })

                valid = True

                # Constraint 5: The person who is an engineer is Peter.
                # Enforce both ways: if occupation is engineer, name must be Peter and if name is Peter, occupation must be engineer.
                for house in candidate:
                    if house["Occupation"] == "engineer" and house["Name"] != "Peter":
                        valid = False
                        break
                    if house["Name"] == "Peter" and house["Occupation"] != "engineer":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 4: The photography enthusiast is the person who is a teacher.
                # So, if someone is teacher then their hobby must be photography and vice versa.
                for house in candidate:
                    if house["Occupation"] == "teacher" and house["Hobby"] != "photography":
                        valid = False
                        break
                    if house["Hobby"] == "photography" and house["Occupation"] != "teacher":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 2: The person who loves cooking is directly left of the person who is a teacher.
                # That means in some adjacent pair, the house on the left has hobby "cooking" and the house on the right has occupation "teacher".
                pair_found = False
                for i in range(len(candidate) - 1):
                    if candidate[i]["Hobby"] == "cooking" and candidate[i+1]["Occupation"] == "teacher":
                        pair_found = True
                        break
                if not pair_found:
                    continue

                # Constraint 1: The person who is a doctor and Eric are next to each other.
                idx_doctor = None
                idx_eric = None
                for i in range(3):
                    if candidate[i]["Occupation"] == "doctor":
                        idx_doctor = i
                    if candidate[i]["Name"] == "Eric":
                        idx_eric = i
                if idx_doctor is None or idx_eric is None or abs(idx_doctor - idx_eric) != 1:
                    continue

                # Constraint 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
                idx_gardening = None
                # Reassign idx_doctor (it was assigned already above but reusing is safe)
                for i in range(3):
                    if candidate[i]["Hobby"] == "gardening":
                        idx_gardening = i
                if idx_doctor is None or idx_gardening is None or not (idx_doctor > idx_gardening):
                    continue

                # If all constraints are satisfied, return the candidate solution.
                return candidate

    return None

def main():
    solution_candidate = solve_puzzle()
    # Build the output structure as required.
    output = {"solution": {"header": ["House", "Name", "Occupation", "Hobby"], "rows": []}}
    if solution_candidate:
        # Ensure the rows are in the order of House 1, House 2, House 3.
        sorted_solution = sorted(solution_candidate, key=lambda x: x["House"])
        for house in sorted_solution:
            row = [str(house["House"]), house["Name"], house["Occupation"], house["Hobby"]]
            output["solution"]["rows"].append(row)
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()