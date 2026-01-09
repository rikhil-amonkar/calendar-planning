import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthdays = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]
    
    # Add variables for each house (1-4)
    for i in range(1, 5):
        problem.addVariable(f"name_{i}", names)
        problem.addVariable(f"hobby_{i}", hobbies)
        problem.addVariable(f"birthday_{i}", birthdays)
        problem.addVariable(f"education_{i}", educations)
        problem.addVariable(f"smoothie_{i}", smoothies)
    
    # All attributes must be different within each category
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"name_{i}" for i in range(1, 5)])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"hobby_{i}" for i in range(1, 5)])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"birthday_{i}" for i in range(1, 5)])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"education_{i}" for i in range(1, 5)])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"smoothie_{i}" for i in range(1, 5)])
    
    # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
    for i in range(1, 5):
        problem.addConstraint(
            lambda smoothie, birthday: not (smoothie == "desert" and birthday != "jan") and 
                                      not (birthday == "jan" and smoothie != "desert"),
            [f"smoothie_{i}", f"birthday_{i}"]
        )
    
    # Clue 2: Eric is the person with a bachelor's degree.
    for i in range(1, 5):
        problem.addConstraint(
            lambda name, education: not (name == "Eric" and education != "bachelor") and 
                                   not (education == "bachelor" and name != "Eric"),
            [f"name_{i}", f"education_{i}"]
        )
    
    # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
    # (Already implied by clues 1 and 2, but let's add it explicitly)
    for i in range(1, 5):
        problem.addConstraint(
            lambda birthday, education: not (birthday == "jan" and education != "bachelor") and 
                                       not (education == "bachelor" and birthday != "jan"),
            [f"birthday_{i}", f"education_{i}"]
        )
    
    # Clue 4: The person with a high school diploma is in the third house.
    problem.addConstraint(lambda education: education == "high school", ["education_3"])
    
    # Clue 5: The Watermelon smoothie lover is not in the third house.
    problem.addConstraint(lambda smoothie: smoothie != "watermelon", ["smoothie_3"])
    
    # Clue 6: The person with an associate's degree is Arnold.
    for i in range(1, 5):
        problem.addConstraint(
            lambda name, education: not (name == "Arnold" and education != "associate") and 
                                   not (education == "associate" and name != "Arnold"),
            [f"name_{i}", f"education_{i}"]
        )
    
    # Clue 7: The person with a master's degree is the person who paints as a hobby.
    for i in range(1, 5):
        problem.addConstraint(
            lambda education, hobby: not (education == "master" and hobby != "painting") and 
                                    not (hobby == "painting" and education != "master"),
            [f"education_{i}", f"hobby_{i}"]
        )
    
    # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
    dragonfruit_positions = [f"smoothie_{i}" for i in range(1, 5)]
    sept_birthday_positions = [f"birthday_{i}" for i in range(1, 5)]
    
    def one_house_between_constraint(s1, s2, s3, s4, b1, b2, b3, b4):
        dragonfruit_house = None
        sept_birthday_house = None
        
        for i, smoothie in enumerate([s1, s2, s3, s4]):
            if smoothie == "dragonfruit":
                dragonfruit_house = i + 1
                
        for i, birthday in enumerate([b1, b2, b3, b4]):
            if birthday == "sept":
                sept_birthday_house = i + 1
                
        if dragonfruit_house is not None and sept_birthday_house is not None:
            return abs(dragonfruit_house - sept_birthday_house) == 2
        return True
    
    problem.addConstraint(one_house_between_constraint, 
                         dragonfruit_positions + sept_birthday_positions)
    
    # Clue 9: The person with a high school diploma is the person whose birthday is in September.
    problem.addConstraint(lambda education, birthday: education == "high school" and birthday == "sept", 
                         ["education_3", "birthday_3"])
    
    # Clue 10: The person who loves cooking is Alice.
    for i in range(1, 5):
        problem.addConstraint(
            lambda hobby, name: not (hobby == "cooking" and name != "Alice") and 
                               not (name == "Alice" and hobby != "cooking"),
            [f"hobby_{i}", f"name_{i}"]
        )
    
    # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
    april_positions = [f"birthday_{i}" for i in range(1, 5)]
    gardening_positions = [f"hobby_{i}" for i in range(1, 5)]
    
    def adjacent_constraint(b1, b2, b3, b4, h1, h2, h3, h4):
        april_house = None
        gardening_house = None
        
        for i, birthday in enumerate([b1, b2, b3, b4]):
            if birthday == "april":
                april_house = i + 1
                
        for i, hobby in enumerate([h1, h2, h3, h4]):
            if hobby == "gardening":
                gardening_house = i + 1
                
        if april_house is not None and gardening_house is not None:
            return abs(april_house - gardening_house) == 1
        return True
    
    problem.addConstraint(adjacent_constraint, april_positions + gardening_positions)
    
    # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
    for i in range(1, 5):
        problem.addConstraint(
            lambda hobby, birthday: not (hobby == "painting" and birthday != "feb") and 
                                   not (birthday == "feb" and hobby != "painting"),
            [f"hobby_{i}", f"birthday_{i}"]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"]
    rows = []
    
    for i in range(1, 5):
        row = [
            str(i),
            solution[f"name_{i}"],
            solution[f"hobby_{i}"],
            solution[f"birthday_{i}"],
            solution[f"education_{i}"],
            solution[f"smoothie_{i}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))