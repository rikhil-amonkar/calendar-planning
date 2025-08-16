from z3 import *
import json

def main():
    s = Solver()
    houses = 3

    # Create variables for each attribute for each house.
    # For each house, the variables take values in {0, 1, 2}:
    # Names: 0: Arnold, 1: Eric, 2: Peter
    # Animals: 0: bird, 1: horse, 2: cat
    # Birthdays: 0: jan, 1: sept, 2: april
    # Hobbies: 0: photography, 1: cooking, 2: gardening
    # Drinks: 0: milk, 1: water, 2: tea
    # Hair Colors: 0: blonde, 1: brown, 2: black
    names = [Int(f"name_{i}") for i in range(houses)]
    animals = [Int(f"animal_{i}") for i in range(houses)]
    birthdays = [Int(f"birthday_{i}") for i in range(houses)]
    hobbies = [Int(f"hobby_{i}") for i in range(houses)]
    drinks = [Int(f"drink_{i}") for i in range(houses)]
    hair = [Int(f"hair_{i}") for i in range(houses)]

    # Domain constraints: Each variable must be in 0..2.
    for i in range(houses):
        s.add(And(names[i] >= 0, names[i] <= 2))
        s.add(And(animals[i] >= 0, animals[i] <= 2))
        s.add(And(birthdays[i] >= 0, birthdays[i] <= 2))
        s.add(And(hobbies[i] >= 0, hobbies[i] <= 2))
        s.add(And(drinks[i] >= 0, drinks[i] <= 2))
        s.add(And(hair[i] >= 0, hair[i] <= 2))

    # All attributes are unique across houses.
    s.add(Distinct(names))
    s.add(Distinct(animals))
    s.add(Distinct(birthdays))
    s.add(Distinct(hobbies))
    s.add(Distinct(drinks))
    s.add(Distinct(hair))

    #--------------------------------------------------------------------------
    # Clues in natural language and their translations:
    #
    # 1. "The person who has brown hair is the person who loves cooking."
    #    (brown hair = 1  and cooking = 1)
    #
    # 2. "The person whose birthday is in April is in the third house."
    #    (april = 2) so house 3 (index 2) gets birthday 2.
    #
    # 3. "Eric is not in the first house."
    #    (Eric = 1) so house 1 (index 0) ≠ 1.
    #
    # 4. "The cat lover is in the second house."
    #    (cat = 2) so house 2 (index 1) gets animal 2.
    #
    # 5. "The person who has blonde hair is somewhere to the left of the person who likes milk."
    #    (blonde = 0; milk = 0) so the unique house with hair==0 must have an index less than the unique house with drink==0.
    #
    # 6. "The person who enjoys gardening is the person who likes milk."
    #    (gardening = 2, milk = 0) so gardening and milk are equivalent.
    #
    # 7. "The cat lover is the person who has brown hair."
    #    (cat = 2 and brown = 1) so animal==2 if and only if hair==1.
    #
    # 8. "Arnold is the bird keeper."
    #    (Arnold = 0; bird = 0) so if name==0 then animal==0.
    #
    # 9. "The one who only drinks water is the photography enthusiast."
    #    (water = 1; photography = 0) so drink==1 if and only if hobby==0.
    #
    # 10. "The person whose birthday is in September is directly left of Arnold."
    #     (sept = 1) so for any house (except the first), if the house holds Arnold (name==0),
    #     then the immediately preceding house must have birthday==1.
    #--------------------------------------------------------------------------

    # Clue 3 and Clue 10 imply that Arnold cannot be in the first house.
    s.add(names[0] != 0)   # Arnold = 0 cannot be in house1
    s.add(names[0] != 1)   # Also, Eric (1) is not in the first house.
    # As a consequence, house1 (index 0) must be Peter (2).

    # Clue 2: House 3 (index 2) birthday is April (2)
    s.add(birthdays[2] == 2)

    # Clue 4: The cat lover (cat = 2) is in the second house (index 1)
    s.add(animals[1] == 2)

    # Now add clues that apply individually for each house.
    for i in range(houses):
        # Clue 1: brown hair (1) <=> cooking (1)
        s.add(Implies(hair[i] == 1, hobbies[i] == 1))
        s.add(Implies(hobbies[i] == 1, hair[i] == 1))

        # Clue 6: gardening (2) <=> milk (0)
        s.add(Implies(hobbies[i] == 2, drinks[i] == 0))
        s.add(Implies(drinks[i] == 0, hobbies[i] == 2))

        # Clue 9: photography (0) <=> water (1)
        s.add(Implies(drinks[i] == 1, hobbies[i] == 0))
        s.add(Implies(hobbies[i] == 0, drinks[i] == 1))

        # Clue 7: cat lover (animal 2) <=> brown hair (1)
        s.add(Implies(animals[i] == 2, hair[i] == 1))
        s.add(Implies(hair[i] == 1, animals[i] == 2))

        # Clue 8: Arnold (0) is the bird keeper (0).
        s.add(Implies(names[i] == 0, animals[i] == 0))

        # Clue 10: The person with birthday in September (1) is directly left of Arnold.
        if i > 0:
            s.add(Implies(names[i] == 0, birthdays[i - 1] == 1))

    # Clue 5: The person with blonde hair (0) is somewhere to the left of the person who likes milk (0).
    for i in range(houses):
        for j in range(houses):
            # If house i drinks milk and house j has blonde hair, then j must come before i.
            s.add(Implies(And(drinks[i] == 0, hair[j] == 0), j < i))

    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()

        # Maps to convert numeric values back to the corresponding strings.
        name_map = {0: "Arnold", 1: "Eric", 2: "Peter"}
        animal_map = {0: "bird", 1: "horse", 2: "cat"}
        birthday_map = {0: "jan", 1: "sept", 2: "april"}
        hobby_map = {0: "photography", 1: "cooking", 2: "gardening"}
        drink_map = {0: "milk", 1: "water", 2: "tea"}
        hair_map = {0: "blonde", 1: "brown", 2: "black"}

        solution_rows = []
        for i in range(houses):
            row = []
            # House numbers are 1-indexed in the output.
            row.append(str(i + 1))
            row.append(name_map[m[names[i]].as_long()])
            row.append(animal_map[m[animals[i]].as_long()])
            row.append(birthday_map[m[birthdays[i]].as_long()])
            row.append(hobby_map[m[hobbies[i]].as_long()])
            row.append(drink_map[m[drinks[i]].as_long()])
            row.append(hair_map[m[hair[i]].as_long()])
            solution_rows.append(row)

        result = {
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()