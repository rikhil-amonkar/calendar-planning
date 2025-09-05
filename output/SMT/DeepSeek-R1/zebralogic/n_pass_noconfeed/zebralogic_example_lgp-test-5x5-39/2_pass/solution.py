import z3
import json

def main():
    # Create the solver
    solver = z3.Solver()

    # Define the attributes with enums and get both sort and constants
    Name_sort, name_consts = z3.EnumSort('Name', ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold'])
    Birthday_sort, birthday_consts = z3.EnumSort('Birthday', ['mar', 'april', 'sept', 'feb', 'jan'])
    Mother_sort, mother_consts = z3.EnumSort('Mother', ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya'])
    Occupation_sort, occupation_consts = z3.EnumSort('Occupation', ['engineer', 'doctor', 'lawyer', 'artist', 'teacher'])
    HairColor_sort, hair_color_consts = z3.EnumSort('HairColor', ['red', 'blonde', 'black', 'gray', 'brown'])

    # Unpack the constants
    Alice, Eric, Bob, Peter, Arnold = name_consts
    mar, april, sept, feb, jan = birthday_consts
    Holly, Janelle, Kailyn, Penny, Aniya = mother_consts
    engineer, doctor, lawyer, artist, teacher = occupation_consts
    red, blonde, black, gray, brown = hair_color_consts

    # Create variables for each house (index 0 to 4 for house 1 to 5)
    names = [z3.Const(f'name_{i}', Name_sort) for i in range(5)]
    birthdays = [z3.Const(f'birthday_{i}', Birthday_sort) for i in range(5)]
    mothers = [z3.Const(f'mother_{i}', Mother_sort) for i in range(5)]
    occupations = [z3.Const(f'occupation_{i}', Occupation_sort) for i in range(5)]
    hair_colors = [z3.Const(f'hair_color_{i}', HairColor_sort) for i in range(5)]

    # Each attribute must have distinct values across houses
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(birthdays))
    solver.add(z3.Distinct(mothers))
    solver.add(z3.Distinct(occupations))
    solver.add(z3.Distinct(hair_colors))

    # Add constraints from clues
    # 1. The person whose birthday is in March is in the fifth house.
    solver.add(birthdays[4] == mar)
    
    # 2. The person whose birthday is in February is in the first house.
    solver.add(birthdays[0] == feb)
    
    # 3. The person who is a doctor is Eric.
    for i in range(5):
        solver.add(z3.Implies(occupations[i] == doctor, names[i] == Eric))
    
    # 4. The person whose mother's name is Janelle is in the third house.
    solver.add(mothers[2] == Janelle)
    
    # 5. The person who is an artist is the person who has brown hair.
    for i in range(5):
        solver.add(z3.Implies(occupations[i] == artist, hair_colors[i] == brown))
    
    # 6. The person who is an artist is in the fourth house.
    solver.add(occupations[3] == artist)
    
    # 7. The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    black_hair_index = z3.Int('black_hair_index')
    penny_mother_index = z3.Int('penny_mother_index')
    solver.add(penny_mother_index < black_hair_index)
    for i in range(5):
        solver.add(z3.Implies(mothers[i] == Penny, penny_mother_index == i))
        solver.add(z3.Implies(hair_colors[i] == black, black_hair_index == i))
    
    # 8. Peter is the person who has black hair.
    for i in range(5):
        solver.add(z3.Implies(hair_colors[i] == black, names[i] == Peter))
    
    # 9. The person who has gray hair is the person who is a teacher.
    for i in range(5):
        solver.add(z3.Implies(hair_colors[i] == gray, occupations[i] == teacher))
    
    # 10. Alice is The person whose mother's name is Kailyn.
    for i in range(5):
        solver.add(z3.Implies(mothers[i] == Kailyn, names[i] == Alice))
    
    # 11. Arnold is somewhere to the right of the person whose birthday is in September.
    sept_bday_index = z3.Int('sept_bday_index')
    arnold_index = z3.Int('arnold_index')
    solver.add(sept_bday_index < arnold_index)
    for i in range(5):
        solver.add(z3.Implies(birthdays[i] == sept, sept_bday_index == i))
        solver.add(z3.Implies(names[i] == Arnold, arnold_index == i))
    
    # 12. The person who has brown hair is the person whose birthday is in January.
    for i in range(5):
        solver.add(z3.Implies(hair_colors[i] == brown, birthdays[i] == jan))
    
    # 13. Arnold is the person who has blonde hair.
    for i in range(5):
        solver.add(z3.Implies(names[i] == Arnold, hair_colors[i] == blonde))
    
    # 14. The person whose mother's name is Holly is the person who has black hair.
    for i in range(5):
        solver.add(z3.Implies(mothers[i] == Holly, hair_colors[i] == black))
    
    # 15. Peter is the person who is a lawyer.
    for i in range(5):
        solver.add(z3.Implies(names[i] == Peter, occupations[i] == lawyer))
    
    # 16. The person whose birthday is in September is somewhere to the left of The person whose mother's name is Kailyn.
    kailyn_mother_index = z3.Int('kailyn_mother_index')
    solver.add(sept_bday_index < kailyn_mother_index)
    for i in range(5):
        solver.add(z3.Implies(mothers[i] == Kailyn, kailyn_mother_index == i))
    
    # 17. Alice is the person who has gray hair.
    for i in range(5):
        solver.add(z3.Implies(names[i] == Alice, hair_colors[i] == gray))

    # Check if the solver can solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract values for each house
        result = []
        for i in range(5):
            name_val = model.eval(names[i])
            birthday_val = model.eval(birthdays[i])
            mother_val = model.eval(mothers[i])
            occupation_val = model.eval(occupations[i])
            hair_color_val = model.eval(hair_colors[i])
            
            # Convert to string and remove the trailing quotes from the enum representation
            row = [
                str(i+1),
                str(name_val).replace('"', ''),
                str(birthday_val).replace('"', ''),
                str(mother_val).replace('"', ''),
                str(occupation_val).replace('"', ''),
                str(hair_color_val).replace('"', '')
            ]
            result.append(row)
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()