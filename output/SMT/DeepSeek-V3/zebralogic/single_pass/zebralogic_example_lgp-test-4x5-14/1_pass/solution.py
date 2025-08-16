from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the attributes
    names = ["Peter", "Alice", "Eric", "Arnold"]
    mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
    smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
    heights = ["tall", "average", "short", "very short"]
    educations = ["high school", "associate", "master", "bachelor"]

    # Create variables for each attribute in each house
    name = {h: String(f"name_{h}") for h in houses}
    mother = {h: String(f"mother_{h}") for h in houses}
    smoothie = {h: String(f"smoothie_{h}") for h in houses}
    height = {h: String(f"height_{h}") for h in houses}
    education = {h: String(f"education_{h}") for h in houses}

    # Add constraints that each attribute is one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([mother[h] == m for m in mothers]))
        s.add(Or([smoothie[h] == sm for sm in smoothies]))
        s.add(Or([height[h] == ht for ht in heights]))
        s.add(Or([education[h] == ed for ed in educations]))

    # Add uniqueness constraints for each attribute across houses
    for attr in [name, mother, smoothie, height, education]:
        for h1 in houses:
            for h2 in houses:
                if h1 < h2:
                    s.add(attr[h1] != attr[h2])

    # Add constraints from the clues
    # Clue 1: The person whose mother's name is Janelle is in the third house.
    s.add(mother[3] == "Janelle")

    # Clue 2: The Desert smoothie lover is the person with a master's degree.
    for h in houses:
        s.add(Implies(smoothie[h] == "desert", education[h] == "master"))

    # Clue 3: The Desert smoothie lover is not in the first house.
    s.add(smoothie[1] != "desert")

    # Clue 4: The person who is very short is somewhere to the left of the person with a high school diploma.
    # This means there exists h1 < h2 where height[h1] == "very short" and education[h2] == "high school"
    very_short_left_of_high_school = Or([
        And(height[h1] == "very short", education[h2] == "high school", h1 < h2)
        for h1 in houses for h2 in houses
    ])
    s.add(very_short_left_of_high_school)

    # Clue 5: Eric and the person who likes Cherry smoothies are next to each other.
    # This means for some h, Eric is in h and cherry is in h+1 or h-1, or vice versa
    eric_next_to_cherry = Or([
        And(name[h] == "Eric", smoothie[h+1] == "cherry") for h in houses if h < 4
    ] + [
        And(name[h] == "Eric", smoothie[h-1] == "cherry") for h in houses if h > 1
    ] + [
        And(smoothie[h] == "cherry", name[h+1] == "Eric") for h in houses if h < 4
    ] + [
        And(smoothie[h] == "cherry", name[h-1] == "Eric") for h in houses if h > 1
    ])
    s.add(eric_next_to_cherry)

    # Clue 6: The person with a high school diploma is not in the third house.
    s.add(education[3] != "high school")

    # Clue 7: The person whose mother's name is Kailyn is the person with an associate's degree.
    for h in houses:
        s.add(Implies(mother[h] == "Kailyn", education[h] == "associate"))

    # Clue 8: The person who likes Cherry smoothies is the person whose mother's name is Aniya.
    for h in houses:
        s.add(Implies(smoothie[h] == "cherry", mother[h] == "Aniya"))

    # Clue 9: The person who is tall is the person whose mother's name is Janelle.
    for h in houses:
        s.add(Implies(height[h] == "tall", mother[h] == "Janelle"))

    # Clue 10: Arnold is somewhere to the right of the person who has an average height.
    # This means there exists h1 < h2 where height[h1] == "average" and name[h2] == "Arnold"
    arnold_right_of_average = Or([
        And(height[h1] == "average", name[h2] == "Arnold", h1 < h2)
        for h1 in houses for h2 in houses
    ])
    s.add(arnold_right_of_average)

    # Clue 11: The Dragonfruit smoothie lover is directly left of the person who is short.
    # This means for some h, smoothie[h] == "dragonfruit" and height[h+1] == "short"
    dragonfruit_left_of_short = Or([
        And(smoothie[h] == "dragonfruit", height[h+1] == "short")
        for h in houses if h < 4
    ])
    s.add(dragonfruit_left_of_short)

    # Clue 12: The person who is tall is Alice.
    for h in houses:
        s.add(Implies(height[h] == "tall", name[h] == "Alice"))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                "rows": []
            }
        }
        for h in sorted(houses):
            row = [
                str(h),
                str(model.eval(name[h])),
                str(model.eval(mother[h])),
                str(model.eval(smoothie[h])),
                str(model.eval(height[h])),
                str(model.eval(education[h]))
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"error": "No solution found"}

# Print the solution as JSON
import json
print(json.dumps(solve_scheduling_problem(), indent=2))