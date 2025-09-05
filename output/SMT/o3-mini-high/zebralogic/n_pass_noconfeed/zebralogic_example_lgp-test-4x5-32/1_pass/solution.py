from z3 import *
import json

def main():
    solver = Solver()
    N = 4  # number of houses

    # Create arrays for each attribute (0-indexed houses)
    names = [Int(f"name_{i}") for i in range(N)]
    hobbies = [Int(f"hobby_{i}") for i in range(N)]
    birthdays = [Int(f"birthday_{i}") for i in range(N)]
    educations = [Int(f"education_{i}") for i in range(N)]
    smoothies = [Int(f"smoothie_{i}") for i in range(N)]

    # All variables must be in the range 0 to 3
    variables = names + hobbies + birthdays + educations + smoothies
    for var in variables:
        solver.add(var >= 0, var <= 3)

    # All attributes must be all-different across houses within their category.
    solver.add(Distinct(names))
    solver.add(Distinct(hobbies))
    solver.add(Distinct(birthdays))
    solver.add(Distinct(educations))
    solver.add(Distinct(smoothies))

    # Mappings (we use integers for each attribute)
    # Names: Arnold=0, Alice=1, Eric=2, Peter=3
    ARNOLD, ALICE, ERIC, PETER = 0, 1, 2, 3

    # Hobbies: cooking=0, painting=1, photography=2, gardening=3
    COOKING, PAINTING, PHOTOGRAPHY, GARDENING = 0, 1, 2, 3

    # Birthdays: april=0, jan=1, sept=2, feb=3
    APRIL, JAN, SEPT, FEB = 0, 1, 2, 3

    # Educations: master=0, bachelor=1, associate=2, high school=3
    MASTER, BACHELOR, ASSOCIATE, HIGH_SCHOOL = 0, 1, 2, 3

    # Smoothies: cherry=0, watermelon=1, desert=2, dragonfruit=3
    CHERRY, WATERMELON, DESERT, DRAGONFRUIT = 0, 1, 2, 3

    # Clue 1:
    # The Desert smoothie lover is the person whose birthday is in January.
    # <=> For each house: smoothie == DESERT if and only if birthday == JAN.
    for i in range(N):
        solver.add(Implies(smoothies[i] == DESERT, birthdays[i] == JAN))
        solver.add(Implies(birthdays[i] == JAN, smoothies[i] == DESERT))

    # Clue 2:
    # Eric is the person with a bachelor's degree.
    for i in range(N):
        solver.add(Implies(names[i] == ERIC, educations[i] == BACHELOR))

    # Clue 3:
    # The person whose birthday is in January is the person with a bachelor's degree.
    for i in range(N):
        solver.add(Implies(birthdays[i] == JAN, educations[i] == BACHELOR))
        solver.add(Implies(educations[i] == BACHELOR, birthdays[i] == JAN))

    # Clue 4:
    # The person with a high school diploma is in the third house (house number 3, index 2).
    solver.add(educations[2] == HIGH_SCHOOL)

    # Clue 5:
    # The Watermelon smoothie lover is not in the third house.
    solver.add(smoothies[2] != WATERMELON)

    # Clue 6:
    # The person with an associate's degree is Arnold.
    for i in range(N):
        solver.add(Implies(names[i] == ARNOLD, educations[i] == ASSOCIATE))
        solver.add(Implies(educations[i] == ASSOCIATE, names[i] == ARNOLD))

    # Clue 7:
    # The person with a master's degree is the person who paints as a hobby.
    for i in range(N):
        solver.add(Implies(educations[i] == MASTER, hobbies[i] == PAINTING))
        solver.add(Implies(hobbies[i] == PAINTING, educations[i] == MASTER))

    # Clue 8:
    # There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
    # For any houses i and j that satisfy these conditions, |i - j| must equal 2.
    for i in range(N):
        for j in range(N):
            solver.add(Implies(And(smoothies[i] == DRAGONFRUIT, birthdays[j] == SEPT), Abs(i - j) == 2))

    # Clue 9:
    # The person with the high school diploma is the person whose birthday is in September.
    for i in range(N):
        solver.add(Implies(educations[i] == HIGH_SCHOOL, birthdays[i] == SEPT))
        solver.add(Implies(birthdays[i] == SEPT, educations[i] == HIGH_SCHOOL))

    # Clue 10:
    # The person who loves cooking is Alice.
    for i in range(N):
        solver.add(Implies(hobbies[i] == COOKING, names[i] == ALICE))
        solver.add(Implies(names[i] == ALICE, hobbies[i] == COOKING))

    # Clue 11:
    # The person whose birthday is in April and the person who enjoys gardening are next to each other.
    for i in range(N):
        for j in range(N):
            solver.add(Implies(And(birthdays[i] == APRIL, hobbies[j] == GARDENING), Abs(i - j) == 1))

    # Clue 12:
    # The person who paints as a hobby is the person whose birthday is in February.
    for i in range(N):
        solver.add(Implies(hobbies[i] == PAINTING, birthdays[i] == FEB))
        solver.add(Implies(birthdays[i] == FEB, hobbies[i] == PAINTING))

    # Additional domain constraints based on uniqueness:
    # Each house must have a unique birthday. Since the available birthdays are APRIL, JAN, SEPT, FEB,
    # if we have assigned JAN, SEPT, and FEB to houses elsewhere, the remaining one must be APRIL.
    # Similarly for other categories but the Distinct constraint covers that.

    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()
        # Determine the remaining values by elimination:
        # For birthdays: Houses with indices 1,2,3 might be fixed by clues.
        # House 2 (index 1): if a house gets DESERT then birthday must be JAN,
        # and house 2 (index 2) is HIGH_SCHOOL so birthday = SEPT,
        # and if a house is MASTER (and PAINTING) then birthday = FEB.
        # The remaining birthday (APRIL) goes to the remaining house.
        # Similarly, for smoothies: House with DESERT (paired with JAN) and DRAGONFRUIT must be one house separated by two from SEPT.
        # The remaining smoothies are CHERRY and WATERMELON but clue 5 prevents WATERMELON in house 3 (index 2).
        # By the constraints, the following unique solution is determined:
        #
        # House 1 (index 0): 
        #   Name: Arnold (associate), Birthday: APRIL, Hobby: PHOTOGRAPHY, Smoothie: DRAGONFRUIT
        # House 2 (index 1): 
        #   Name: Eric (bachelor), Birthday: JAN, Hobby: GARDENING, Smoothie: DESERT
        # House 3 (index 2): 
        #   Name: Alice (high school), Birthday: SEPT, Hobby: COOKING, Smoothie: CHERRY
        # House 4 (index 3): 
        #   Name: Peter (master), Birthday: FEB, Hobby: PAINTING, Smoothie: WATERMELON
        #
        # Now prepare the JSON output.
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": []
            }
        }
        
        name_map = {ARNOLD: "Arnold", ALICE: "Alice", ERIC: "Eric", PETER: "Peter"}
        hobby_map = {COOKING: "cooking", PAINTING: "painting", PHOTOGRAPHY: "photography", GARDENING: "gardening"}
        birthday_map = {APRIL: "april", JAN: "jan", SEPT: "sept", FEB: "feb"}
        education_map = {MASTER: "master", BACHELOR: "bachelor", ASSOCIATE: "associate", HIGH_SCHOOL: "high school"}
        smoothie_map = {CHERRY: "cherry", WATERMELON: "watermelon", DESERT: "desert", DRAGONFRUIT: "dragonfruit"}
        
        # Extract the assignment for each house from the model.
        results = []
        for i in range(N):
            house_num = str(i + 1)
            name_val = name_map[model.evaluate(names[i]).as_long()]
            hobby_val = hobby_map[model.evaluate(hobbies[i]).as_long()]
            birthday_val = birthday_map[model.evaluate(birthdays[i]).as_long()]
            education_val = education_map[model.evaluate(educations[i]).as_long()]
            smoothie_val = smoothie_map[model.evaluate(smoothies[i]).as_long()]
            results.append([house_num, name_val, hobby_val, birthday_val, education_val, smoothie_val])
        
        # Because the model variables might not assign the values in the intuitive order,
        # we sort rows by house number (they are already in order since i goes from 0 to N-1).
        solution["solution"]["rows"] = results
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()