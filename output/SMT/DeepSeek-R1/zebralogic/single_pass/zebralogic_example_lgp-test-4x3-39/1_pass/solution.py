import z3

def main():
    # Define enums for Name, HairColor, and FavoriteSport
    NameSort, name_consts = z3.EnumSort('Name', ['Eric', 'Alice', 'Peter', 'Arnold'])
    Eric, Alice, Peter, Arnold = name_consts

    HairSort, hair_consts = z3.EnumSort('Hair', ['blonde', 'black', 'red', 'brown'])
    blonde, black, red, brown = hair_consts

    SportSort, sport_consts = z3.EnumSort('Sport', ['swimming', 'soccer', 'basketball', 'tennis'])
    swimming, soccer, basketball, tennis = sport_consts

    # Arrays for each house: 0-based index for houses 1 to 4
    n = [z3.Const(f'n_{i}', NameSort) for i in range(4)]
    h = [z3.Const(f'h_{i}', HairSort) for i in range(4)]
    s = [z3.Const(f's_{i}', SportSort) for i in range(4)]

    solver = z3.Solver()

    # All names are distinct
    solver.add(z3.Distinct(n))
    # All hair colors are distinct
    solver.add(z3.Distinct(h))
    # All sports are distinct
    solver.add(z3.Distinct(s))

    # Clue 1: The person who loves soccer is not in the second house (index 1)
    solver.add(s[1] != soccer)

    # Clue 2: Eric is the person who has blonde hair.
    for i in range(4):
        solver.add(z3.Implies(n[i] == Eric, h[i] == blonde))

    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    # Find index of basketball lover and blonde hair
    basketball_lover = z3.Int('basketball_lover')
    blonde_hair = z3.Int('blonde_hair')
    solver.add(basketball_lover >= 0, basketball_lover < 4)
    solver.add(blonde_hair >= 0, blonde_hair < 4)
    solver.add(blonde_hair > basketball_lover)
    for i in range(4):
        solver.add(z3.Implies(s[i] == basketball, basketball_lover == i))
        solver.add(z3.Implies(h[i] == blonde, blonde_hair == i))

    # Clue 4: The person who has black hair is the person who loves tennis.
    for i in range(4):
        solver.add(z3.Implies(h[i] == black, s[i] == tennis))

    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    arnold_index = z3.Int('arnold_index')
    red_hair_index = z3.Int('red_hair_index')
    solver.add(arnold_index >= 0, arnold_index < 4)
    solver.add(red_hair_index >= 0, red_hair_index < 4)
    solver.add(red_hair_index > arnold_index)
    for i in range(4):
        solver.add(z3.Implies(n[i] == Arnold, arnold_index == i))
        solver.add(z3.Implies(h[i] == red, red_hair_index == i))

    # Clue 6: Alice is the person who loves swimming.
    for i in range(4):
        solver.add(z3.Implies(n[i] == Alice, s[i] == swimming))

    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    for i in range(3):  # Check from 0 to 2 (since next is i+1)
        solver.add(z3.Implies(h[i] == red, h[i+1] == black))
    # Also ensure that if red is at position i, black must be at i+1 and not elsewhere
    solver.add(z3.Or([z3.And(h[i] == red, h[i+1] == black) for i in range(3)]))

    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract the values for each house
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = model.eval(n[i])
            hair_val = model.eval(h[i])
            sport_val = model.eval(s[i])
            # Convert to string by matching with the constants
            name_str = str(name_val)
            hair_str = str(hair_val)
            sport_str = str(sport_val)
            rows.append([house_num, name_str, hair_str, sport_str])
        
        # Prepare the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
        }
        
        # Output as JSON string
        import json
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()