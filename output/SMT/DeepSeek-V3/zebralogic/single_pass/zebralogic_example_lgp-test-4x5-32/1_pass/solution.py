from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the attributes
    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthdays = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    # Create variables for each attribute in each house
    name = {h: String(f"name_{h}") for h in houses}
    hobby = {h: String(f"hobby_{h}") for h in houses}
    birthday = {h: String(f"birthday_{h}") for h in houses}
    education = {h: String(f"education_{h}") for h in houses}
    smoothie = {h: String(f"smoothie_{h}") for h in houses}

    # Add constraints that each attribute is one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([hobby[h] == ho for ho in hobbies]))
        s.add(Or([birthday[h] == b for b in birthdays]))
        s.add(Or([education[h] == e for e in educations]))
        s.add(Or([smoothie[h] == sm for sm in smoothies]))

    # Add constraints that all attributes in each category are distinct
    s.add(Distinct([name[h] for h in houses]))
    s.add(Distinct([hobby[h] for h in houses]))
    s.add(Distinct([birthday[h] for h in houses]))
    s.add(Distinct([education[h] for h in houses]))
    s.add(Distinct([smoothie[h] for h in houses]))

    # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
    for h in houses:
        s.add(Implies(smoothie[h] == "desert", birthday[h] == "jan"))

    # Clue 2: Eric is the person with a bachelor's degree.
    for h in houses:
        s.add(Implies(name[h] == "Eric", education[h] == "bachelor"))

    # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
    for h in houses:
        s.add(Implies(birthday[h] == "jan", education[h] == "bachelor"))

    # Clue 4: The person with a high school diploma is in the third house.
    s.add(education[3] == "high school")

    # Clue 5: The Watermelon smoothie lover is not in the third house.
    for h in houses:
        if h == 3:
            s.add(smoothie[h] != "watermelon")

    # Clue 6: The person with an associate's degree is Arnold.
    for h in houses:
        s.add(Implies(name[h] == "Arnold", education[h] == "associate"))

    # Clue 7: The person with a master's degree is the person who paints as a hobby.
    for h in houses:
        s.add(Implies(education[h] == "master", hobby[h] == "painting"))

    # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
    # This means if Dragonfruit is in 1, sept is in 3; if Dragonfruit is in 2, sept is in 4.
    # Dragonfruit cannot be in 3 or 4 because there's no house after with one in between.
    s.add(Or(
        And(smoothie[1] == "dragonfruit", birthday[3] == "sept"),
        And(smoothie[2] == "dragonfruit", birthday[4] == "sept")
    ))

    # Clue 9: The person with a high school diploma is the person whose birthday is in September.
    s.add(birthday[3] == "sept")  # From clue 4, high school is in house 3
    # So birthday in house 3 is sept (from clue 9)

    # Clue 10: The person who loves cooking is Alice.
    for h in houses:
        s.add(Implies(hobby[h] == "cooking", name[h] == "Alice"))

    # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
    # This means they are in consecutive houses, either (1 and 2) or (2 and 3) or (3 and 4)
    s.add(Or(
        And(birthday[1] == "april", hobby[2] == "gardening"),
        And(birthday[2] == "april", hobby[1] == "gardening"),
        And(birthday[2] == "april", hobby[3] == "gardening"),
        And(birthday[3] == "april", hobby[2] == "gardening"),
        And(birthday[3] == "april", hobby[4] == "gardening"),
        And(birthday[4] == "april", hobby[3] == "gardening")
    ))

    # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
    for h in houses:
        s.add(Implies(hobby[h] == "painting", birthday[h] == "feb"))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": []
            }
        }
        for h in sorted(houses):
            row = [
                str(h),
                str(model.eval(name[h])),
                str(model.eval(hobby[h])),
                str(model.eval(birthday[h])),
                str(model.eval(education[h])),
                str(model.eval(smoothie[h]))
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": [], "rows": []}}

# Print the solution as JSON
import json
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))