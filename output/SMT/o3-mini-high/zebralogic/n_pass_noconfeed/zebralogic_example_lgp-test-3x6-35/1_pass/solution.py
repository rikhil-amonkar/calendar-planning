from z3 import *
import json

def solve_zebra():
    s = Solver()
    num_houses = 3

    # Each attribute is represented as an integer in the set {0, 1, 2}.
    # Mappings:
    # Name:      Eric = 0, Arnold = 1, Peter = 2
    # Vacation:  mountain = 0, city = 1, beach = 2
    # Height:    very short = 0, average = 1, short = 2
    # Flower:    carnations = 0, daffodils = 1, lilies = 2
    # HairColor: brown = 0, black = 1, blonde = 2
    # Education: associate = 0, bachelor = 1, high school = 2

    names = [Int(f"name_{i}") for i in range(num_houses)]
    vacations = [Int(f"vacation_{i}") for i in range(num_houses)]
    heights = [Int(f"height_{i}") for i in range(num_houses)]
    flowers = [Int(f"flower_{i}") for i in range(num_houses)]
    haircolors = [Int(f"haircolor_{i}") for i in range(num_houses)]
    educations = [Int(f"education_{i}") for i in range(num_houses)]

    # Domain constraints: each variable is in {0,1,2}
    for var in names + vacations + heights + flowers + haircolors + educations:
        s.add(var >= 0, var < num_houses)

    # All attributes are all-different across the houses.
    s.add(Distinct(names))
    s.add(Distinct(vacations))
    s.add(Distinct(heights))
    s.add(Distinct(flowers))
    s.add(Distinct(haircolors))
    s.add(Distinct(educations))

    # String representations for output.
    name_str = ["Eric", "Arnold", "Peter"]
    vacation_str = ["mountain", "city", "beach"]
    height_str = ["very short", "average", "short"]
    flower_str = ["carnations", "daffodils", "lilies"]
    hair_str = ["brown", "black", "blonde"]
    education_str = ["associate", "bachelor", "high school"]

    # Clue 1: Peter is the person who has an average height.
    # Peter -> 2, average height -> 1.
    for i in range(num_houses):
        s.add(Implies(names[i] == 2, heights[i] == 1))

    # Clue 2: The person who loves a bouquet of daffodils is Arnold.
    # daffodils -> 1, Arnold -> 1.
    for i in range(num_houses):
        s.add(Implies(flowers[i] == 1, names[i] == 1))
        s.add(Implies(names[i] == 1, flowers[i] == 1))

    # Clue 3: The person who is very short is not in the second house.
    # Second house is index 1, very short -> 0.
    s.add(heights[1] != 0)

    # Clue 4: The person who loves beach vacations is in the first house.
    # First house is index 0, beach -> 2.
    s.add(vacations[0] == 2)

    # Clue 5: The person with a high school diploma is in the third house.
    # Third house is index 2, high school -> 2.
    s.add(educations[2] == 2)

    # Clue 6: The person who is short is somewhere to the right of the person who is very short.
    # short -> 2, very short -> 0.
    # Ensure that the house with "very short" is not the rightmost and that the house
    # with "short" comes later.
    s.add(heights[2] != 0)
    s.add(Implies(heights[0] == 0, Or(heights[1] == 2, heights[2] == 2)))
    s.add(Implies(heights[1] == 0, heights[2] == 2))

    # Clue 7: The person who loves the bouquet of lilies is Eric.
    # lilies -> 2, Eric -> 0.
    for i in range(num_houses):
        s.add(Implies(flowers[i] == 2, names[i] == 0))
        s.add(Implies(names[i] == 0, flowers[i] == 2))

    # Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
    # bachelor's -> 1.
    for i in range(num_houses):
        s.add(Implies(flowers[i] == 2, educations[i] == 1))
        s.add(Implies(educations[i] == 1, flowers[i] == 2))

    # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
    # city -> 1, Peter -> 2.
    for i in range(num_houses):
        for j in range(num_houses):
            if i != j:
                s.add(Implies(And(names[i] == 2, vacations[j] == 1), i < j))

    # Clue 10: The person who has blonde hair is in the third house.
    # Third house is index 2, blonde -> 2.
    s.add(haircolors[2] == 2)

    # Clue 11: The person who loves beach vacations is the person who has brown hair.
    # beach -> 2, brown -> 0.
    for i in range(num_houses):
        s.add(Implies(vacations[i] == 2, haircolors[i] == 0))
        s.add(Implies(haircolors[i] == 0, vacations[i] == 2))

    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                "rows": []
            }
        }
        # Houses are numbered from 1 to 3 (left to right).
        for i in range(num_houses):
            row = [
                str(i + 1),
                name_str[m[names[i]].as_long()],
                vacation_str[m[vacations[i]].as_long()],
                height_str[m[heights[i]].as_long()],
                flower_str[m[flowers[i]].as_long()],
                hair_str[m[haircolors[i]].as_long()],
                education_str[m[educations[i]].as_long()]
            ]
            solution["solution"]["rows"].append(row)
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found."}))

if __name__ == "__main__":
    solve_zebra()