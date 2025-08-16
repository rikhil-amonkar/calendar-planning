import json
from z3 import *

def solve_puzzle():
    # House indices are 1..4 from left to right
    HOUSES = range(1, 5)

    # Create Z3 Int variables for each attribute value indicating its house position
    # Names
    Peter, AliceN, Eric, Arnold = Ints('Peter Alice Eric Arnold')
    names = [Peter, AliceN, Eric, Arnold]
    name_labels = ["Peter", "Alice", "Eric", "Arnold"]

    # Mothers
    Janelle, Holly, Aniya, Kailyn = Ints('Janelle Holly Aniya Kailyn')
    mothers = [Janelle, Holly, Aniya, Kailyn]
    mother_labels = ["Janelle", "Holly", "Aniya", "Kailyn"]

    # Smoothies
    Watermelon, Dragonfruit, Desert, Cherry = Ints('Watermelon Dragonfruit Desert Cherry')
    smoothies = [Watermelon, Dragonfruit, Desert, Cherry]
    smoothie_labels = ["watermelon", "dragonfruit", "desert", "cherry"]

    # Heights
    Tall, Average, Short, VeryShort = Ints('Tall Average Short VeryShort')
    heights = [Tall, Average, Short, VeryShort]
    height_labels = ["tall", "average", "short", "very short"]

    # Educations
    HighSchool, Associate, Master, Bachelor = Ints('HighSchool Associate Master Bachelor')
    educations = [HighSchool, Associate, Master, Bachelor]
    education_labels = ["high school", "associate", "master", "bachelor"]

    s = Solver()

    # Domain constraints: all variables in 1..4
    for var in names + mothers + smoothies + heights + educations:
        s.add(And(var >= 1, var <= 4))

    # All-different constraints within each category
    s.add(Distinct(names))
    s.add(Distinct(mothers))
    s.add(Distinct(smoothies))
    s.add(Distinct(heights))
    s.add(Distinct(educations))

    # Clues:
    # 1. The person whose mother's name is Janelle is in the third house.
    s.add(Janelle == 3)

    # 2. The Desert smoothie lover is the person with a master's degree.
    s.add(Desert == Master)

    # 3. The Desert smoothie lover is not in the first house.
    s.add(Desert != 1)

    # 4. The person who is very short is somewhere to the left of the person with a high school diploma.
    s.add(VeryShort < HighSchool)

    # 5. Eric and the person who likes Cherry smoothies are next to each other.
    s.add(Or(Eric == Cherry + 1, Eric + 1 == Cherry))

    # 6. The person with a high school diploma is not in the third house.
    s.add(HighSchool != 3)

    # 7. The person whose mother's name is Kailyn is the person with an associate's degree.
    s.add(Kailyn == Associate)

    # 8. The person who likes Cherry smoothies is The person whose mother's name is Aniya.
    s.add(Cherry == Aniya)

    # 9. The person who is tall is The person whose mother's name is Janelle.
    s.add(Tall == Janelle)

    # 10. Arnold is somewhere to the right of the person who has an average height.
    s.add(Arnold > Average)

    # 11. The Dragonfruit smoothie lover is directly left of the person who is short.
    s.add(Dragonfruit + 1 == Short)

    # 12. The person who is tall is Alice.
    s.add(Tall == AliceN)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper: invert mapping to get the label at each house for a category
    def labels_by_house(vars_list, labels):
        inv = {}
        for var, label in zip(vars_list, labels):
            inv[m[var].as_long()] = label
        return [inv[h] for h in HOUSES]

    names_by_house = labels_by_house(names, name_labels)
    mothers_by_house = labels_by_house(mothers, mother_labels)
    smoothies_by_house = labels_by_house(smoothies, smoothie_labels)
    heights_by_house = labels_by_house(heights, height_labels)
    educations_by_house = labels_by_house(educations, education_labels)

    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
            "rows": []
        }
    }

    for i in HOUSES:
        solution["solution"]["rows"].append([
            str(i),
            names_by_house[i - 1],
            mothers_by_house[i - 1],
            smoothies_by_house[i - 1],
            heights_by_house[i - 1],
            educations_by_house[i - 1],
        ])

    print(json.dumps(solution, indent=2))


if __name__ == "__main__":
    solve_puzzle()