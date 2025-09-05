import json
from itertools import permutations

def main():
    # Define the domains
    houses = [1, 2, 3]
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for occ_perm in permutations(occupations):
                # Create assignment for each house
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        "name": name_perm[i],
                        "education": edu_perm[i],
                        "occupation": occ_perm[i]
                    }
                
                # Check clue 1: The person who is a teacher is directly left of the person with an associate's degree.
                clue1_valid = False
                for house in [1, 2]:
                    if (assignment[house]["occupation"] == "teacher" and 
                        assignment[house + 1]["education"] == "associate"):
                        clue1_valid = True
                        break
                if not clue1_valid:
                    continue
                
                # Check clue 2: The person with an associate's degree and Eric are next to each other.
                clue2_valid = False
                # Find house with associate's degree
                associate_house = None
                for house in houses:
                    if assignment[house]["education"] == "associate":
                        associate_house = house
                        break
                
                # Find house with Eric
                eric_house = None
                for house in houses:
                    if assignment[house]["name"] == "Eric":
                        eric_house = house
                        break
                
                if associate_house is not None and eric_house is not None:
                    if abs(associate_house - eric_house) == 1:
                        clue2_valid = True
                if not clue2_valid:
                    continue
                
                # Check clue 3: Peter is the person with a high school diploma.
                clue3_valid = False
                for house in houses:
                    if (assignment[house]["name"] == "Peter" and 
                        assignment[house]["education"] == "high school"):
                        clue3_valid = True
                        break
                if not clue3_valid:
                    continue
                
                # Check clue 4: The person who is a doctor is the person with a bachelor's degree.
                clue4_valid = True
                for house in houses:
                    if (assignment[house]["occupation"] == "doctor" and 
                        assignment[house]["education"] != "bachelor"):
                        clue4_valid = False
                        break
                    if (assignment[house]["education"] == "bachelor" and 
                        assignment[house]["occupation"] != "doctor"):
                        clue4_valid = False
                        break
                if not clue4_valid:
                    continue
                
                # If we reach here, all clues are satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Education", "Occupation"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment.keys()):
                    row = [
                        str(house),
                        assignment[house]["name"],
                        assignment[house]["education"],
                        assignment[house]["occupation"]
                    ]
                    solution["solution"]["rows"].append(row)
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return
    
    # If no solution found
    print(json.dumps({"solution": {"header": ["House", "Name", "Education", "Occupation"], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()