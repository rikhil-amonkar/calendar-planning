import z3
import json

def solve():
    # Define EnumSorts
    Name, (Eric, Alice, Peter, Arnold) = z3.EnumSort('Name', ['Eric', 'Alice', 'Peter', 'Arnold'])
    HairColor, (blonde, black, red, brown) = z3.EnumSort('HairColor', ['blonde', 'black', 'red', 'brown'])
    Sport, (swimming, soccer, basketball, tennis) = z3.EnumSort('Sport', ['swimming', 'soccer', 'basketball', 'tennis'])

    # Create variables for each house (1-4)
    name = [z3.Const(f'name_{i+1}', Name) for i in range(4)]
    hair_color = [z3.Const(f'hair_color_{i+1}', HairColor) for i in range(4)]
    sport = [z3.Const(f'sport_{i+1}', Sport) for i in range(4)]

    s = z3.Solver()

    # Add distinct constraints
    s.add(z3.Distinct(name))
    s.add(z3.Distinct(hair_color))
    s.add(z3.Distinct(sport))

    # Add clues
    # Clue 1: The person who loves soccer is not in the second house.
    s.add(sport[1] != soccer)

    # Clue 2: Eric is the person who has blonde hair.
    for i in range(4):
        s.add(z3.Implies(name[i] == Eric, hair_color[i] == blonde))

    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    for i in range(4):
        for j in range(4):
            s.add(z3.Implies(z3.And(hair_color[i] == blonde, sport[j] == basketball), i > j))

    # Clue 4: The person who has black hair is the person who loves tennis.
    for k in range(4):
        s.add(z3.Implies(hair_color[k] == black, sport[k] == tennis))

    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    for i in range(4):
        for j in range(4):
            s.add(z3.Implies(z3.And(name[i] == Arnold, hair_color[j] == red), i < j))

    # Clue 6: Alice is the person who loves swimming.
    for i in range(4):
        s.add(z3.Implies(name[i] == Alice, sport[i] == swimming))

    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    s.add(z3.Or(
        z3.And(hair_color[0] == red, hair_color[1] == black),
        z3.And(hair_color[1] == red, hair_color[2] == black),
        z3.And(hair_color[2] == red, hair_color[3] == black)
    ))

    # Check satisfiability
    if s.check() == z3.sat:
        model = s.model()
        rows = []
        for i in range(4):
            house_num = i + 1
            name_val = model.evaluate(name[i]).decl().name()
            hair_val = model.evaluate(hair_color[i]).decl().name()
            sport_val = model.evaluate(sport[i]).decl().name()
            rows.append([str(house_num), name_val, hair_val, sport_val])
        return {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
    }
    else:
        return None

# Generate and print the JSON result
result = solve()
print(json.dumps(result, indent=2))