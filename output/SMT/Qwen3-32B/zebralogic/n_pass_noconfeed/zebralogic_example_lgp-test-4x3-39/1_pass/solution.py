from z3 import *
import json

def main():
    # Define enums
    Names, (Eric, Alice, Peter, Arnold) = EnumSort('Names', ['Eric', 'Alice', 'Peter', 'Arnold'])
    HairColors, (blonde, black, red, brown) = EnumSort('HairColors', ['blonde', 'black', 'red', 'brown'])
    Sports, (swimming, soccer, basketball, tennis) = EnumSort('Sports', ['swimming', 'soccer', 'basketball', 'tennis'])

    # Create variables for each house (1-4)
    name = [Const(f'name_{i+1}', Names) for i in range(4)]
    hair = [Const(f'hair_{i+1}', HairColors) for i in range(4)]
    sport = [Const(f'sport_{i+1}', Sports) for i in range(4)]

    solver = Solver()

    # Add distinct constraints for each category
    solver.add(Distinct(name))
    solver.add(Distinct(hair))
    solver.add(Distinct(sport))

    # Clue 1: The person who loves soccer is not in the second house.
    solver.add(sport[1] != soccer)

    # Clue 2: Eric has blonde hair.
    for i in range(4):
        solver.add(Implies(name[i] == Eric, hair[i] == blonde))

    # Clue 3: Blonde is to the right of basketball.
    h_blonde = Int('h_blonde')
    h_basketball = Int('h_basketball')
    for i in range(4):
        solver.add(Implies(hair[i] == blonde, h_blonde == i + 1))
        solver.add(Implies(sport[i] == basketball, h_basketball == i + 1))
    solver.add(And(1 <= h_blonde, h_blonde <= 4))
    solver.add(And(1 <= h_basketball, h_basketball <= 4))
    solver.add(h_blonde > h_basketball)

    # Clue 4: Black hair loves tennis.
    for i in range(4):
        solver.add(Implies(hair[i] == black, sport[i] == tennis))

    # Clue 5: Arnold is to the left of red hair.
    h_arnold = Int('h_arnold')
    h_red = Int('h_red')
    for i in range(4):
        solver.add(Implies(name[i] == Arnold, h_arnold == i + 1))
        solver.add(Implies(hair[i] == red, h_red == i + 1))
    solver.add(And(1 <= h_arnold, h_arnold <= 4))
    solver.add(And(1 <= h_red, h_red <= 4))
    solver.add(h_arnold < h_red)

    # Clue 6: Alice loves swimming.
    for i in range(4):
        solver.add(Implies(name[i] == Alice, sport[i] == swimming))

    # Clue 7: Red hair is directly left of black hair.
    h_black = Int('h_black')
    for i in range(4):
        solver.add(Implies(hair[i] == black, h_black == i + 1))
    solver.add(And(1 <= h_black, h_black <= 4))
    solver.add(h_black == h_red + 1)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        # Extract the values for each house
        rows = []
        for i in range(4):
            house_num = i + 1
            name_val = model.eval(name[i])
            hair_val = model.eval(hair[i])
            sport_val = model.eval(sport[i])
            rows.append([str(house_num), str(name_val), str(hair_val), str(sport_val)])
        # Build the JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()