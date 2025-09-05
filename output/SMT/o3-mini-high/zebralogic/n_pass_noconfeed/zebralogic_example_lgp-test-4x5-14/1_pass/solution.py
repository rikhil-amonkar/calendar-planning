from z3 import *
import json

def main():
    solver = Solver()
    houses = range(4)

    # Create variables for each attribute in each house.
    name = [Int(f"name_{i}") for i in houses]
    mother = [Int(f"mother_{i}") for i in houses]
    smoothie = [Int(f"smoothie_{i}") for i in houses]
    height = [Int(f"height_{i}") for i in houses]
    education = [Int(f"education_{i}") for i in houses]

    # Domain constraints for each variable (0 to 3).
    for i in houses:
        solver.add(And(name[i] >= 0, name[i] < 4))
        solver.add(And(mother[i] >= 0, mother[i] < 4))
        solver.add(And(smoothie[i] >= 0, smoothie[i] < 4))
        solver.add(And(height[i] >= 0, height[i] < 4))
        solver.add(And(education[i] >= 0, education[i] < 4))

    # All attributes are unique (they form permutations).
    solver.add(Distinct(name))
    solver.add(Distinct(mother))
    solver.add(Distinct(smoothie))
    solver.add(Distinct(height))
    solver.add(Distinct(education))

    # Mapping indices for our attributes:
    # Names: 0:Peter, 1:Alice, 2:Eric, 3:Arnold
    # Mothers: 0:Janelle, 1:Holly, 2:Aniya, 3:Kailyn
    # Smoothies: 0:watermelon, 1:dragonfruit, 2:desert, 3:cherry
    # Heights: 0:tall, 1:average, 2:short, 3:very short
    # Education: 0:high school, 1:associate, 2:master, 3:bachelor

    # Clue 1: The person whose mother's name is Janelle is in the third house (house index 2).
    solver.add(mother[2] == 0)

    # Clue 2: The Desert smoothie lover (2) is the person with a master's degree (2).
    for i in houses:
        solver.add((smoothie[i] == 2) == (education[i] == 2))

    # Clue 3: The Desert smoothie lover is not in the first house (index 0).
    solver.add(smoothie[0] != 2)

    # Clue 4: The person who is very short (3) is somewhere to the left of the person with a high school diploma (0).
    for i in houses:
        for j in houses:
            solver.add(Implies(And(height[i] == 3, education[j] == 0), i < j))

    # Clue 5: Eric (2) and the person who likes Cherry smoothies (3) are next to each other.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(name[i] == 2, smoothie[j] == 3), Or(j == i + 1, j == i - 1)))

    # Clue 6: The person with a high school diploma (0) is not in the third house (index 2).
    solver.add(education[2] != 0)

    # Clue 7: The person whose mother's name is Kailyn (3) is the person with an associate's degree (1).
    for i in houses:
        solver.add((mother[i] == 3) == (education[i] == 1))

    # Clue 8: The person who likes Cherry smoothies (3) is the person whose mother's name is Aniya (2).
    for i in houses:
        solver.add((smoothie[i] == 3) == (mother[i] == 2))

    # Clue 9: The person who is tall (0) is the person whose mother's name is Janelle (0).
    for i in houses:
        solver.add((height[i] == 0) == (mother[i] == 0))

    # Clue 10: Arnold (3) is somewhere to the right of the person who has an average height (1).
    for i in houses:
        for j in houses:
            solver.add(Implies(And(name[i] == 3, height[j] == 1), j < i))

    # Clue 11: The Dragonfruit smoothie lover (1) is directly left of the person who is short (2).
    # For houses 0 to 2, if a house has dragonfruit then the next house must have short.
    for i in range(3):
        solver.add(Implies(smoothie[i] == 1, height[i + 1] == 2))
    # Also, the last house cannot have the dragonfruit smoothie.
    solver.add(smoothie[3] != 1)

    # Clue 12: The person who is tall (0) is Alice (1).
    for i in houses:
        solver.add((height[i] == 0) == (name[i] == 1))

    # Solve the constraints.
    if solver.check() == sat:
        m = solver.model()
        # Define the value mappings for output.
        names_list = ["Peter", "Alice", "Eric", "Arnold"]
        mothers_list = ["Janelle", "Holly", "Aniya", "Kailyn"]
        smoothies_list = ["watermelon", "dragonfruit", "desert", "cherry"]
        heights_list = ["tall", "average", "short", "very short"]
        education_list = ["high school", "associate", "master", "bachelor"]

        rows = []
        for i in houses:
            house_number = str(i + 1)
            name_val = m.evaluate(name[i]).as_long()
            mother_val = m.evaluate(mother[i]).as_long()
            smoothie_val = m.evaluate(smoothie[i]).as_long()
            height_val = m.evaluate(height[i]).as_long()
            education_val = m.evaluate(education[i]).as_long()

            row = [
                house_number,
                names_list[name_val],
                mothers_list[mother_val],
                smoothies_list[smoothie_val],
                heights_list[height_val],
                education_list[education_val]
            ]
            rows.append(row)

        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        # If no solution is found, output an empty JSON structure.
        print(json.dumps({"solution": {"header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()