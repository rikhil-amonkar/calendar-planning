import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house
    houses = [1, 2]
    
    # Add variables for each attribute
    for house in houses:
        problem.addVariable(f"name_{house}", ["Arnold", "Eric"])
        problem.addVariable(f"occupation_{house}", ["engineer", "doctor"])
        problem.addVariable(f"birthday_{house}", ["april", "sept"])
        problem.addVariable(f"house_style_{house}", ["victorian", "colonial"])
        problem.addVariable(f"height_{house}", ["very short", "short"])
        problem.addVariable(f"cigar_{house}", ["pall mall", "prince"])
    
    # All attributes must be unique across houses
    for attr in ["name", "occupation", "birthday", "house_style", "height", "cigar"]:
        problem.addConstraint(lambda *args: len(set(args)) == len(args), 
                            [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The person who is an engineer is in the first house.
    problem.addConstraint(lambda occupation_1, occupation_2: occupation_1 == "engineer", 
                         ["occupation_1", "occupation_2"])
    
    # Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
    # Since there are only 2 houses, they must be adjacent by definition
    problem.addConstraint(lambda birthday_1, birthday_2, occupation_1, occupation_2: 
                         (birthday_1 == "april" and occupation_2 == "doctor") or 
                         (birthday_2 == "april" and occupation_1 == "doctor"),
                         ["birthday_1", "birthday_2", "occupation_1", "occupation_2"])
    
    # Clue 3: The person living in a colonial-style house is the person who is an engineer.
    problem.addConstraint(lambda house_style_1, house_style_2, occupation_1, occupation_2: 
                         (house_style_1 == "colonial" and occupation_1 == "engineer") or 
                         (house_style_2 == "colonial" and occupation_2 == "engineer"),
                         ["house_style_1", "house_style_2", "occupation_1", "occupation_2"])
    
    # Clue 4: The person who is very short is the person who is an engineer.
    problem.addConstraint(lambda height_1, height_2, occupation_1, occupation_2: 
                         (height_1 == "very short" and occupation_1 == "engineer") or 
                         (height_2 == "very short" and occupation_2 == "engineer"),
                         ["height_1", "height_2", "occupation_1", "occupation_2"])
    
    # Clue 5: The person who is short is the person partial to Pall Mall.
    problem.addConstraint(lambda height_1, height_2, cigar_1, cigar_2: 
                         (height_1 == "short" and cigar_1 == "pall mall") or 
                         (height_2 == "short" and cigar_2 == "pall mall"),
                         ["height_1", "height_2", "cigar_1", "cigar_2"])
    
    # Clue 6: The person who is an engineer is Eric.
    problem.addConstraint(lambda name_1, name_2, occupation_1, occupation_2: 
                         (occupation_1 == "engineer" and name_1 == "Eric") or 
                         (occupation_2 == "engineer" and name_2 == "Eric"),
                         ["name_1", "name_2", "occupation_1", "occupation_2"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution (should be only one)
    solution = solutions[0]
    
    # Format the solution as required
    header = ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"occupation_{house}"],
            solution[f"birthday_{house}"],
            solution[f"house_style_{house}"],
            solution[f"height_{house}"],
            solution[f"cigar_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))