from z3 import *

def main():
    s = Solver()

    houses = [1, 2, 3, 4]
    n_houses = len(houses)

    names = [Int(f'name_{i}') for i in houses]
    hobbies = [Int(f'hobby_{i}') for i in houses]
    birthdays = [Int(f'birthday_{i}') for i in houses]
    educations = [Int(f'education_{i}') for i in houses]
    smoothies = [Int(f'smoothie_{i}') for i in houses]

    for i in range(n_houses):
        s.add(names[i] >= 0, names[i] <= 3)
        s.add(hobbies[i] >= 0, hobbies[i] <= 3)
        s.add(birthdays[i] >= 0, birthdays[i] <= 3)
        s.add(educations[i] >= 0, educations[i] <= 3)
        s.add(smoothies[i] >= 0, smoothies[i] <= 3)

    s.add(Distinct(names))
    s.add(Distinct(hobbies))
    s.add(Distinct(birthdays))
    s.add(Distinct(educations))
    s.add(Distinct(smoothies))

    # Clue 1: Desert smoothie lover is birthday January.
    for i in range(n_houses):
        s.add((smoothies[i] == 2) == (birthdays[i] == 1))

    # Clue 2: Eric is bachelor.
    for i in range(n_houses):
        s.add(Implies(names[i] == 2, educations[i] == 1))

    # Clue 3: January birthday is bachelor.
    for i in range(n_houses):
        s.add((birthdays[i] == 1) == (educations[i] == 1))

    # Clue 4: High school diploma in third house.
    s.add(educations[2] == 3)

    # Clue 5: Watermelon smoothie not in third house.
    s.add(smoothies[2] != 1)

    # Clue 6: Associate degree is Arnold.
    for i in range(n_houses):
        s.add(Implies(names[i] == 0, educations[i] == 2))

    # Clue 7: Master degree is painting hobby.
    for i in range(n_houses):
        s.add((educations[i] == 0) == (hobbies[i] == 1))

    # Clue 8: One house between dragonfruit and september birthday.
    s.add(Or(
        And(smoothies[0] == 3, birthdays[2] == 2),
        And(smoothies[1] == 3, birthdays[3] == 2),
        And(smoothies[2] == 3, birthdays[0] == 2),
        And(smoothies[3] == 3, birthdays[1] == 2)
    ))

    # Clue 9: High school diploma is september birthday.
    for i in range(n_houses):
        s.add((educations[i] == 3) == (birthdays[i] == 2))

    # Clue 10: Cooking hobby is Alice.
    for i in range(n_houses):
        s.add((hobbies[i] == 0) == (names[i] == 1))

    # Clue 11: April birthday and gardening hobby are adjacent.
    s.add(Or(
        And(birthdays[0] == 0, hobbies[1] == 3),
        And(birthdays[1] == 0, hobbies[0] == 3),
        And(birthdays[1] == 0, hobbies[2] == 3),
        And(birthdays[2] == 0, hobbies[1] == 3),
        And(birthdays[2] == 0, hobbies[3] == 3),
        And(birthdays[3] == 0, hobbies[2] == 3)
    ))

    # Clue 12: Painting hobby is feb birthday.
    for i in range(n_houses):
        s.add((hobbies[i] == 1) == (birthdays[i] == 3))

    if s.check() == sat:
        model = s.model()

        names_map = {0: "Arnold", 1: "Alice", 2: "Eric", 3: "Peter"}
        hobbies_map = {0: "cooking", 1: "painting", 2: "photography", 3: "gardening"}
        birthdays_map = {0: "april", 1: "jan", 2: "sept", 3: "feb"}
        educations_map = {0: "master", 1: "bachelor", 2: "associate", 3: "high school"}
        smoothies_map = {0: "cherry", 1: "watermelon", 2: "desert", 3: "dragonfruit"}

        rows = []
        for i in range(n_houses):
            name_val = model.evaluate(names[i]).as_long()
            hobby_val = model.evaluate(hobbies[i]).as_long()
            birthday_val = model.evaluate(birthdays[i]).as_long()
            education_val = model.evaluate(educations[i]).as_long()
            smoothie_val = model.evaluate(smoothies[i]).as_long()
            
            row = [
                str(i+1),
                names_map[name_val],
                hobbies_map[hobby_val],
                birthdays_map[birthday_val],
                educations_map[education_val],
                smoothies_map[smoothie_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": rows
            }
        }
        
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()