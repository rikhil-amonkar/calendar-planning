def main():
    # Define the attributes for the 3 houses
    houses = [1, 2, 3]
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]
    
    solution = None

    # Iterate over all permutations of the attributes for the houses
    for name_perm in itertools.permutations(names):
        for edu_perm in itertools.permutations(educations):
            for occ_perm in itertools.permutations(occupations):
                config = []
                for i in range(3):
                    # Create a configuration for each house (house numbers as string)
                    config.append({
                        "House": str(houses[i]),
                        "Name": name_perm[i],
                        "Education": edu_perm[i],
                        "Occupation": occ_perm[i]
                    })
                
                valid = True

                # Clue 3: Peter is the person with a high school diploma.
                for entry in config:
                    if entry["Name"] == "Peter" and entry["Education"] != "high school":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 4: The person who is a doctor is the person with a bachelor's degree.
                for entry in config:
                    if entry["Occupation"] == "doctor" and entry["Education"] != "bachelor":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
                teacher_associate_found = False
                for i in range(len(config) - 1):
                    if config[i]["Occupation"] == "teacher" and config[i+1]["Education"] == "associate":
                        teacher_associate_found = True
                        break
                if not teacher_associate_found:
                    continue

                # Clue 2: The person with an associate's degree and Eric are next to each other.
                associate_index = None
                eric_index = None
                for i, entry in enumerate(config):
                    if entry["Education"] == "associate":
                        associate_index = i
                    if entry["Name"] == "Eric":
                        eric_index = i
                if associate_index is None or eric_index is None or abs(associate_index - eric_index) != 1:
                    continue

                # If all constraints are met, record the solution and break out
                solution = config
                break
            if solution:
                break
        if solution:
            break

    # Prepare the final JSON output with the specified structure
    if solution:
        output = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": [
                    [entry["House"], entry["Name"], entry["Education"], entry["Occupation"]] for entry in solution
                ]
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == '__main__':
    main()