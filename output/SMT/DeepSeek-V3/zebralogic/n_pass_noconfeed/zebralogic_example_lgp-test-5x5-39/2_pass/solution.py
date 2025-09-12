import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the attributes and their possible values
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
    birthdays = ['mar', 'april', 'sept', 'feb', 'jan']
    mothers = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
    occupations = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
    hair_colors = ['red', 'blonde', 'black', 'gray', 'brown']
    
    # Create variables for each house (1-5) and each attribute
    name_vars = [Int(f'name_{i}') for i in range(1, 6)]
    birthday_vars = [Int(f'birthday_{i}') for i in range(1, 6)]
    mother_vars = [Int(f'mother_{i}') for i in range(1, 6)]
    occupation_vars = [Int(f'occupation_{i}') for i in range(1, 6)]
    hair_color_vars = [Int(f'hair_color_{i}') for i in range(1, 6)]
    
    # Define the domain for each variable (0-4 for the 5 possible values)
    for i in range(5):
        s.add(name_vars[i] >= 0, name_vars[i] < 5)
        s.add(birthday_vars[i] >= 0, birthday_vars[i] < 5)
        s.add(mother_vars[i] >= 0, mother_vars[i] < 5)
        s.add(occupation_vars[i] >= 0, occupation_vars[i] < 5)
        s.add(hair_color_vars[i] >= 0, hair_color_vars[i] < 5)
    
    # All attributes within each category must be distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(birthday_vars))
    s.add(Distinct(mother_vars))
    s.add(Distinct(occupation_vars))
    s.add(Distinct(hair_color_vars))
    
    # Clue 1: The person whose birthday is in March is in the fifth house.
    s.add(birthday_vars[4] == birthdays.index('mar'))
    
    # Clue 2: The person whose birthday is in February is in the first house.
    s.add(birthday_vars[0] == birthdays.index('feb'))
    
    # Clue 3: The person who is a doctor is Eric.
    for i in range(5):
        s.add(Implies(occupation_vars[i] == occupations.index('doctor'), name_vars[i] == names.index('Eric')))
    
    # Clue 4: The person whose mother's name is Janelle is in the third house.
    s.add(mother_vars[2] == mothers.index('Janelle'))
    
    # Clue 5: The person who is an artist is the person who has brown hair.
    for i in range(5):
        s.add(occupation_vars[i] == occupations.index('artist') == (hair_color_vars[i] == hair_colors.index('brown')))
    
    # Clue 6: The person who is an artist is in the fourth house.
    s.add(occupation_vars[3] == occupations.index('artist'))
    
    # Clue 7: The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    penny_indices = [If(mother_vars[i] == mothers.index('Penny'), i, -1) for i in range(5)]
    black_hair_indices = [If(hair_color_vars[i] == hair_colors.index('black'), i, -1) for i in range(5)]
    s.add(Exists([i, j], And(i >= 0, j >= 0, i < j, 
                            mother_vars[i] == mothers.index('Penny'), 
                            hair_color_vars[j] == hair_colors.index('black'))))
    
    # Clue 8: Peter is the person who has black hair.
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Peter'), hair_color_vars[i] == hair_colors.index('black')))
    
    # Clue 9: The person who has gray hair is the person who is a teacher.
    for i in range(5):
        s.add(hair_color_vars[i] == hair_colors.index('gray') == (occupation_vars[i] == occupations.index('teacher')))
    
    # Clue 10: Alice is The person whose mother's name is Kailyn.
    for i in range(5):
        s.add(name_vars[i] == names.index('Alice') == (mother_vars[i] == mothers.index('Kailyn')))
    
    # Clue 11: Arnold is somewhere to the right of the person whose birthday is in September.
    sept_indices = [If(birthday_vars[i] == birthdays.index('sept'), i, -1) for i in range(5)]
    arnold_indices = [If(name_vars[i] == names.index('Arnold'), i, -1) for i in range(5)]
    s.add(Exists([i, j], And(i >= 0, j >= 0, i < j, 
                            birthday_vars[i] == birthdays.index('sept'), 
                            name_vars[j] == names.index('Arnold'))))
    
    # Clue 12: The person who has brown hair is the person whose birthday is in January.
    for i in range(5):
        s.add(hair_color_vars[i] == hair_colors.index('brown') == (birthday_vars[i] == birthdays.index('jan')))
    
    # Clue 13: Arnold is the person who has blonde hair.
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Arnold'), hair_color_vars[i] == hair_colors.index('blonde')))
    
    # Clue 14: The person whose mother's name is Holly is the person who has black hair.
    for i in range(5):
        s.add(mother_vars[i] == mothers.index('Holly') == (hair_color_vars[i] == hair_colors.index('black')))
    
    # Clue 15: Peter is the person who is a lawyer.
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Peter'), occupation_vars[i] == occupations.index('lawyer')))
    
    # Clue 16: The person whose birthday is in September is somewhere to the left of The person whose mother's name is Kailyn.
    sept_indices = [If(birthday_vars[i] == birthdays.index('sept'), i, -1) for i in range(5)]
    kailyn_indices = [If(mother_vars[i] == mothers.index('Kailyn'), i, -1) for i in range(5)]
    s.add(Exists([i, j], And(i >= 0, j >= 0, i < j, 
                            birthday_vars[i] == birthdays.index('sept'), 
                            mother_vars[j] == mothers.index('Kailyn'))))
    
    # Clue 17: Alice is the person who has gray hair.
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Alice'), hair_color_vars[i] == hair_colors.index('gray')))
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Extract the solution
        solution = []
        for i in range(5):
            name_idx = model.evaluate(name_vars[i]).as_long()
            birthday_idx = model.evaluate(birthday_vars[i]).as_long()
            mother_idx = model.evaluate(mother_vars[i]).as_long()
            occupation_idx = model.evaluate(occupation_vars[i]).as_long()
            hair_color_idx = model.evaluate(hair_color_vars[i]).as_long()
            
            row = {
                "House": str(i+1),
                "Name": names[name_idx],
                "Birthday": birthdays[birthday_idx],
                "Mother": mothers[mother_idx],
                "Occupation": occupations[occupation_idx],
                "HairColor": hair_colors[hair_color_idx]
            }
            solution.append(row)
        
        # Format the output as JSON
        output = {
            "solution": solution
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()