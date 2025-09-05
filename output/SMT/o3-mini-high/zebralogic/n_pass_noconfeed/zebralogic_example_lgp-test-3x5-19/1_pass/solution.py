from z3 import *
import json

def main():
    houses = 3
    # Create Z3 integer variables for each attribute per house.
    names = [Int(f"name_{i}") for i in range(houses)]
    occupations = [Int(f"occupation_{i}") for i in range(houses)]
    educations = [Int(f"education_{i}") for i in range(houses)]
    smoothies = [Int(f"smoothie_{i}") for i in range(houses)]
    hobbies = [Int(f"hobby_{i}") for i in range(houses)]
    
    s = Solver()

    # Domain constraints: each variable is in {0, 1, 2}.
    for var in names + occupations + educations + smoothies + hobbies:
        s.add(var >= 0, var < 3)
    
    # Uniqueness constraints for each attribute.
    s.add(Distinct(names))
    s.add(Distinct(occupations))
    s.add(Distinct(educations))
    s.add(Distinct(smoothies))
    s.add(Distinct(hobbies))
    
    # Mapping:
    # Names: 0 = "Arnold", 1 = "Peter", 2 = "Eric"
    # Occupations: 0 = "doctor", 1 = "teacher", 2 = "engineer"
    # Educations: 0 = "associate", 1 = "high school", 2 = "bachelor"
    # Smoothies: 0 = "desert", 1 = "cherry", 2 = "watermelon"
    # Hobbies: 0 = "gardening", 1 = "cooking", 2 = "photography"
    
    # Clue 1: The Desert smoothie lover is the person who is a doctor.
    # For each house, smoothie == desert (0) if and only if occupation == doctor (0).
    for i in range(houses):
        s.add(Implies(smoothies[i] == 0, occupations[i] == 0))
        s.add(Implies(occupations[i] == 0, smoothies[i] == 0))
    
    # Clue 2: Arnold is not in the third house.
    s.add(names[2] != 0)
    
    # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
    # Since we fix Peter's house below (clue 5), the only possibility is that the Cherry smoothie (1)
    # must be in a house to the right. With 3 houses and Peter not in the rightmost house, this forces:
    s.add(smoothies[2] == 1)
    
    # Clue 4: The person who loves cooking is in the second house.
    # Cooking corresponds to hobby 1; second house is index 1.
    s.add(hobbies[1] == 1)
    
    # Clue 5: The person who loves cooking is Peter.
    # Enforce that the house with cooking (house index 1) has the name Peter (1).
    s.add(names[1] == 1)
    
    # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    # Associate's degree -> education value 0; gardening -> hobby value 0.
    posGardening = If(hobbies[0] == 0, 0, If(hobbies[1] == 0, 1, 2))
    posAssociate = If(educations[0] == 0, 0, If(educations[1] == 0, 1, 2))
    s.add(posAssociate > posGardening)
    
    # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    # Bachelor's degree -> education value 2; Desert smoothie -> smoothie value 0.
    posBachelor = If(educations[0] == 2, 0, If(educations[1] == 2, 1, 2))
    posDesert = If(smoothies[0] == 0, 0, If(smoothies[1] == 0, 1, 2))
    s.add(posBachelor > posDesert)
    
    # Clue 8: The person who loves cooking is the person who is a doctor.
    # Cooking (hobby 1) <-> doctor (occupation 0).
    for i in range(houses):
        s.add(Implies(hobbies[i] == 1, occupations[i] == 0))
        s.add(Implies(occupations[i] == 0, hobbies[i] == 1))
    
    # Clue 9: The photography enthusiast is the person who is a teacher.
    # Photography (hobby 2) <-> teacher (occupation 1).
    for i in range(houses):
        s.add(Implies(hobbies[i] == 2, occupations[i] == 1))
        s.add(Implies(occupations[i] == 1, hobbies[i] == 2))
    
    # Additionally, enforce the direct equivalence: The person who loves cooking is Peter.
    for i in range(houses):
        s.add(Implies(hobbies[i] == 1, names[i] == 1))
        s.add(Implies(names[i] == 1, hobbies[i] == 1))
    
    # We already used cooking and doctor constraints for house index 1; reinforce:
    s.add(occupations[1] == 0)
    s.add(smoothies[1] == 0)
    
    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()
        # Define mapping dictionaries to convert assigned numbers to words.
        name_map = {0: "Arnold", 1: "Peter", 2: "Eric"}
        occupation_map = {0: "doctor", 1: "teacher", 2: "engineer"}
        education_map = {0: "associate", 1: "high school", 2: "bachelor"}
        smoothie_map = {0: "desert", 1: "cherry", 2: "watermelon"}
        hobby_map = {0: "gardening", 1: "cooking", 2: "photography"}
        
        header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
        rows = []
        for i in range(houses):
            house_num = str(i + 1)
            row = [
                house_num,
                name_map[m.evaluate(names[i]).as_long()],
                occupation_map[m.evaluate(occupations[i]).as_long()],
                education_map[m.evaluate(educations[i]).as_long()],
                smoothie_map[m.evaluate(smoothies[i]).as_long()],
                hobby_map[m.evaluate(hobbies[i]).as_long()]
            ]
            rows.append(row)
        solution = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()