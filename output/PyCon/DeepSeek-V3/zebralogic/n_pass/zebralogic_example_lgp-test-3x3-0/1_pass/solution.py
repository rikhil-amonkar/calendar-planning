import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3]
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"education_{house}", educations)
        problem.addVariable(f"occupation_{house}", occupations)
    
    # All attributes must be different across houses
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"name_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"education_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"occupation_{house}" for house in houses])
    
    # Clue 1: The person who is a teacher is directly left of the person with an associate's degree
    problem.addConstraint(lambda occ1, occ2, occ3, edu1, edu2, edu3: 
                         (occ1 == "teacher" and edu2 == "associate") or 
                         (occ2 == "teacher" and edu3 == "associate"),
                         ["occupation_1", "occupation_2", "occupation_3",
                          "education_1", "education_2", "education_3"])
    
    # Clue 2: The person with an associate's degree and Eric are next to each other
    problem.addConstraint(lambda edu1, edu2, edu3, name1, name2, name3: 
                         (edu1 == "associate" and (name2 == "Eric" or (edu2 == "associate" and name1 == "Eric"))) or
                         (edu2 == "associate" and ((name1 == "Eric" or name3 == "Eric") or (name2 == "Eric" and (edu1 == "associate" or edu3 == "associate")))) or
                         (edu3 == "associate" and (name2 == "Eric" or (edu2 == "associate" and name3 == "Eric"))),
                         ["education_1", "education_2", "education_3",
                          "name_1", "name_2", "name_3"])
    
    # Clue 3: Peter is the person with a high school diploma
    problem.addConstraint(lambda name1, name2, name3, edu1, edu2, edu3: 
                         (name1 == "Peter" and edu1 == "high school") or
                         (name2 == "Peter" and edu2 == "high school") or
                         (name3 == "Peter" and edu3 == "high school"),
                         ["name_1", "name_2", "name_3",
                          "education_1", "education_2", "education_3"])
    
    # Clue 4: The person who is a doctor is the person with a bachelor's degree
    problem.addConstraint(lambda occ1, occ2, occ3, edu1, edu2, edu3: 
                         (occ1 == "doctor" and edu1 == "bachelor") or
                         (occ2 == "doctor" and edu2 == "bachelor") or
                         (occ3 == "doctor" and edu3 == "bachelor"),
                         ["occupation_1", "occupation_2", "occupation_3",
                          "education_1", "education_2", "education_3"])
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Education", "Occupation"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    rows = []
    
    for house in sorted(houses):
        name = solution[f"name_{house}"]
        education = solution[f"education_{house}"]
        occupation = solution[f"occupation_{house}"]
        rows.append([str(house), name, education, occupation])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))