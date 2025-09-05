from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 3
    # Create variables for each attribute per house
    names = [Int(f"name_{i}") for i in range(num_houses)]
    cigars = [Int(f"cigar_{i}") for i in range(num_houses)]
    hobbies = [Int(f"hobby_{i}") for i in range(num_houses)]
    educations = [Int(f"education_{i}") for i in range(num_houses)]
    drinks = [Int(f"drink_{i}") for i in range(num_houses)]

    # Each variable can take a value 0, 1, or 2
    for var in names + cigars + hobbies + educations + drinks:
        solver.add(var >= 0, var < 3)

    # All attributes in a category are unique across houses
    solver.add(Distinct(names))
    solver.add(Distinct(cigars))
    solver.add(Distinct(hobbies))
    solver.add(Distinct(educations))
    solver.add(Distinct(drinks))

    # Mappings:
    # Names: 0=Eric, 1=Peter, 2=Arnold
    # Cigars: 0=blue master, 1=prince, 2=pall mall
    # Hobbies: 0=photography, 1=gardening, 2=cooking
    # Educations: 0=high school, 1=associate, 2=bachelor
    # Drinks: 0=tea, 1=milk, 2=water

    # Clue 1: The person partial to Pall Mall is Peter.
    for i in range(num_houses):
        solver.add(Implies(cigars[i] == 2, names[i] == 1))

    # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
    # (milk is 1; high school is 0)
    solver.add(drinks[2] != 1)  # milk cannot be in the rightmost house
    for i in range(num_houses - 1):
        solver.add(Implies(drinks[i] == 1, educations[i+1] == 0))

    # Clue 3: Eric is the tea drinker. (Eric is 0; tea is 0)
    for i in range(num_houses):
        solver.add(Implies(names[i] == 0, drinks[i] == 0))

    # Clue 4: Arnold and the Prince smoker are next to each other.
    # Arnold is 2; Prince is 1.
    solver.add(Implies(names[0] == 2, cigars[1] == 1))
    solver.add(Implies(names[1] == 2, Or(cigars[0] == 1, cigars[2] == 1)))
    solver.add(Implies(names[2] == 2, cigars[1] == 1))

    # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
    # gardening is 1. Ensure gardening is not in the rightmost house.
    solver.add(Implies(hobbies[2] == 1, False))
    solver.add(Implies(hobbies[0] == 1, Or(cigars[1] == 1, cigars[2] == 1)))
    solver.add(Implies(hobbies[1] == 1, cigars[2] == 1))

    # Clue 6: The person who likes milk is the person with an associate's degree.
    # milk is 1; associate is 1.
    for i in range(num_houses):
        solver.add(Iff(drinks[i] == 1, educations[i] == 1))

    # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
    # bachelor's is 2; photography is 0.
    solver.add(educations[2] != 2)  # Bachelor's cannot be in the rightmost house.
    for i in range(num_houses - 1):
        solver.add(Implies(educations[i] == 2, hobbies[i+1] == 0))

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        # Define mapping dictionaries to get string outputs
        names_map = {0: "Eric", 1: "Peter", 2: "Arnold"}
        cigars_map = {0: "blue master", 1: "prince", 2: "pall mall"}
        hobbies_map = {0: "photography", 1: "gardening", 2: "cooking"}
        educations_map = {0: "high school", 1: "associate", 2: "bachelor"}
        drinks_map = {0: "tea", 1: "milk", 2: "water"}

        rows = []
        for i in range(num_houses):
            house_num = str(i + 1)
            row = [
                house_num,
                names_map[model[names[i]].as_long()],
                cigars_map[model[cigars[i]].as_long()],
                hobbies_map[model[hobbies[i]].as_long()],
                educations_map[model[educations[i]].as_long()],
                drinks_map[model[drinks[i]].as_long()]
            ]
            rows.append(row)

        result = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()