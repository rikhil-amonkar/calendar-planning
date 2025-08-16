import json
from z3 import *

def solve_puzzle():
    # Indices for houses (0..3 correspond to houses 1..4)
    H = range(4)

    # Value encodings
    NAMES = ["Arnold", "Alice", "Eric", "Peter"]
    HOBBIES = ["cooking", "painting", "photography", "gardening"]
    BIRTHDAYS = ["april", "jan", "sept", "feb"]
    EDUCATIONS = ["master", "bachelor", "associate", "high school"]
    SMOOTHIES = ["cherry", "watermelon", "desert", "dragonfruit"]

    # Constants for easier reference
    Arnold, Alice, Eric, Peter = 0, 1, 2, 3
    Cooking, Painting, Photography, Gardening = 0, 1, 2, 3
    April, Jan, Sept, Feb = 0, 1, 2, 3
    Master, Bachelor, Associate, HighSchool = 0, 1, 2, 3
    Cherry, Watermelon, Desert, Dragonfruit = 0, 1, 2, 3

    # Variables per house
    Name = [Int(f"name_{i}") for i in H]
    Hobby = [Int(f"hobby_{i}") for i in H]
    Birthday = [Int(f"birthday_{i}") for i in H]
    Education = [Int(f"education_{i}") for i in H]
    Smoothie = [Int(f"smoothie_{i}") for i in H]

    s = Solver()

    # Domains
    for i in H:
        s.add(And(Name[i] >= 0, Name[i] < 4))
        s.add(And(Hobby[i] >= 0, Hobby[i] < 4))
        s.add(And(Birthday[i] >= 0, Birthday[i] < 4))
        s.add(And(Education[i] >= 0, Education[i] < 4))
        s.add(And(Smoothie[i] >= 0, Smoothie[i] < 4))

    # All-different constraints for each attribute across houses
    s.add(Distinct(Name))
    s.add(Distinct(Hobby))
    s.add(Distinct(Birthday))
    s.add(Distinct(Education))
    s.add(Distinct(Smoothie))

    # Clues:

    # 1. Desert smoothie lover is the person whose birthday is in January.
    for i in H:
        s.add(Implies(Smoothie[i] == Desert, Birthday[i] == Jan))
        s.add(Implies(Birthday[i] == Jan, Smoothie[i] == Desert))

    # 2. Eric is the person with a bachelor's degree.
    for i in H:
        s.add(Implies(Name[i] == Eric, Education[i] == Bachelor))
        s.add(Implies(Education[i] == Bachelor, Name[i] == Eric))  # Combined with clue 3 consistency

    # 3. The person whose birthday is in January is the person with a bachelor's degree.
    for i in H:
        s.add(Implies(Birthday[i] == Jan, Education[i] == Bachelor))
        s.add(Implies(Education[i] == Bachelor, Birthday[i] == Jan))

    # 4. The person with a high school diploma is in the third house. (house index 2)
    s.add(Education[2] == HighSchool)

    # 5. The Watermelon smoothie lover is not in the third house.
    s.add(Smoothie[2] != Watermelon)

    # 6. The person with an associate's degree is Arnold.
    for i in H:
        s.add(Implies(Name[i] == Arnold, Education[i] == Associate))
        s.add(Implies(Education[i] == Associate, Name[i] == Arnold))

    # 7. The person with a master's degree is the person who paints as a hobby.
    for i in H:
        s.add(Implies(Education[i] == Master, Hobby[i] == Painting))
        s.add(Implies(Hobby[i] == Painting, Education[i] == Master))

    # 8. One house between Dragonfruit smoothie lover and the person whose birthday is in September.
    s.add(Or(
        And(Smoothie[0] == Dragonfruit, Birthday[2] == Sept),
        And(Smoothie[1] == Dragonfruit, Birthday[3] == Sept),
        And(Smoothie[2] == Dragonfruit, Birthday[0] == Sept),
        And(Smoothie[3] == Dragonfruit, Birthday[1] == Sept)
    ))

    # 9. The person with a high school diploma is the person whose birthday is in September.
    for i in H:
        s.add(Implies(Education[i] == HighSchool, Birthday[i] == Sept))
        s.add(Implies(Birthday[i] == Sept, Education[i] == HighSchool))

    # 10. The person who loves cooking is Alice.
    for i in H:
        s.add(Implies(Hobby[i] == Cooking, Name[i] == Alice))
        s.add(Implies(Name[i] == Alice, Hobby[i] == Cooking))

    # 11. The person whose birthday is in April and the person who enjoys gardening are next to each other.
    s.add(Or(
        And(Birthday[0] == April, Hobby[1] == Gardening),
        And(Birthday[1] == April, Or(Hobby[0] == Gardening, Hobby[2] == Gardening)),
        And(Birthday[2] == April, Or(Hobby[1] == Gardening, Hobby[3] == Gardening)),
        And(Birthday[3] == April, Hobby[2] == Gardening)
    ))

    # 12. The person who paints as a hobby is the person whose birthday is in February.
    for i in H:
        s.add(Implies(Hobby[i] == Painting, Birthday[i] == Feb))
        s.add(Implies(Birthday[i] == Feb, Hobby[i] == Painting))

    if s.check() != sat:
        raise ValueError("No solution found")

    m = s.model()

    # Build solution output
    rows = []
    for i in H:
        rows.append([
            str(i + 1),
            NAMES[m.evaluate(Name[i]).as_long()],
            HOBBIES[m.evaluate(Hobby[i]).as_long()],
            BIRTHDAYS[m.evaluate(Birthday[i]).as_long()],
            EDUCATIONS[m.evaluate(Education[i]).as_long()],
            SMOOTHIES[m.evaluate(Smoothie[i]).as_long()],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))