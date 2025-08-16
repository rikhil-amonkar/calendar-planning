from z3 import *
import json

def main():
    # Define the enums for each attribute
    Name, (Arnold, Peter, Eric) = EnumSort('Name', ('Arnold', 'Peter', 'Eric'))
    Occupation, (doctor, teacher, engineer) = EnumSort('Occupation', ('doctor', 'teacher', 'engineer'))
    Education, (associate, high_school, bachelor) = EnumSort('Education', ('associate', 'high school', 'bachelor'))
    Smoothie, (desert, cherry, watermelon) = EnumSort('Smoothie', ('desert', 'cherry', 'watermelon'))
    Hobby, (gardening, cooking, photography) = EnumSort('Hobby', ('gardening', 'cooking', 'photography'))

    # Create variables for each house (0: house1, 1: house2, 2: house3)
    names = [Const('name_%d' % i, Name) for i in range(3)]
    occupations = [Const('occupation_%d' % i, Occupation) for i in range(3)]
    educations = [Const('education_%d' % i, Education) for i in range(3)]
    smoothies = [Const('smoothie_%d' % i, Smoothie) for i in range(3)]
    hobbies = [Const('hobby_%d' % i, Hobby) for i in range(3)]

    s = Solver()

    # Add distinct constraints for each attribute
    s.add(Distinct(names))
    s.add(Distinct(occupations))
    s.add(Distinct(educations))
    s.add(Distinct(smoothies))
    s.add(Distinct(hobbies))

    # Clue 1: Desert smoothie lover is the doctor
    for i in range(3):
        s.add( (smoothies[i] == desert) == (occupations[i] == doctor) )

    # Clue 2: Arnold is not in the third house (index2)
    s.add(names[2] != Arnold)

    # Clue 3: Cherry smoothie lover is to the right of Peter
    for i in range(3):
        # If Peter is in house i, then cherry must be in a house j>i
        clause = []
        for j in range(i+1, 3):
            clause.append(smoothies[j] == cherry)
        s.add(Implies(names[i] == Peter, Or(clause) if clause else False))

    # Clue 4: Cooking hobby is in the second house (index1)
    s.add(hobbies[1] == cooking)

    # Clue 5: Cooking hobby is Peter
    for i in range(3):
        s.add( (hobbies[i] == cooking) == (names[i] == Peter) )

    # Clue 6: Associate degree is to the right of gardening hobby
    for i in range(3):
        clause = []
        for j in range(i+1, 3):
            clause.append(educations[j] == associate)
        s.add(Implies(hobbies[i] == gardening, Or(clause) if clause else False))

    # Clue 7: Bachelor degree is to the right of desert smoothie lover
    for i in range(3):
        clause = []
        for j in range(i+1, 3):
            clause.append(educations[j] == bachelor)
        s.add(Implies(smoothies[i] == desert, Or(clause) if clause else False))

    # Clue 8: Cooking hobby is the doctor
    for i in range(3):
        s.add( (hobbies[i] == cooking) == (occupations[i] == doctor) )

    # Clue 9: Photography hobby is the teacher
    for i in range(3):
        s.add( (hobbies[i] == photography) == (occupations[i] == teacher) )

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            name_val = str(m.eval(names[i]))
            occ_val = str(m.eval(occupations[i]))
            edu_val = str(m.eval(educations[i]))
            smoothie_val = str(m.eval(smoothies[i]))
            hobby_val = str(m.eval(hobbies[i]))
            rows.append([str(i+1), name_val, occ_val, edu_val, smoothie_val, hobby_val])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()