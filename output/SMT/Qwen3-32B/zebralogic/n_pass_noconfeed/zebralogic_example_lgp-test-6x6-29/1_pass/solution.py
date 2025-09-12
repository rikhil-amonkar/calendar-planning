import z3
import json

def solve_puzzle():
    s = z3.Solver()

    # Define variables for each house (1-6, 0-based index)
    names = [z3.String(f"name_{i+1}") for i in range(6)]
    house_styles = [z3.String(f"house_style_{i+1}") for i in range(6)]
    foods = [z3.String(f"food_{i+1}") for i in range(6)]
    vacations = [z3.String(f"vacation_{i+1}") for i in range(6)]
    heights = [z3.String(f"height_{i+1}") for i in range(6)]
    cigars = [z3.String(f"cigar_{i+1}") for i in range(6)]

    # Add uniqueness constraints
    for lst in [names, house_styles, foods, vacations, heights, cigars]:
        s.add(z3.Distinct(lst))

    # Clue 1: Alice is in the fifth house (index 4)
    s.add(names[4] == "Alice")

    # Clue 3: Alice's food is spaghetti
    s.add(foods[4] == "spaghetti")

    # Clue 9: Eric is in the fourth house (index 3)
    s.add(names[3] == "Eric")

    # Clue 4: Arnold's food is stew
    for i in range(6):
        s.add(z3.Implies(names[i] == "Arnold", foods[i] == "stew"))

    # Clue 2: stir fry is in colonial
    for i in range(6):
        s.add(z3.Implies(foods[i] == "stir fry", house_styles[i] == "colonial"))

    # Clue 7: average height is stir fry
    for i in range(6):
        s.add(z3.Implies(foods[i] == "stir fry", heights[i] == "average"))

    # Clue 17: stir fry is directly left of Bob
    for i in range(5):  # i can be 0-4
        s.add(z3.Implies(foods[i] == "stir fry", names[i+1] == "Bob"))

    # Clue 5: average height and Peter have one house between
    for i in range(6):
        for j in range(6):
            s.add(z3.Implies(z3.And(foods[i] == "stir fry", names[j] == "Peter"), z3.Or(j == i + 2, i == j + 2)))

    # Clue 6: Craftsman not in third house (index 2)
    s.add(house_styles[2] != "craftsman")

    # Clue 8: beach vacation is ranch
    for i in range(6):
        s.add(z3.Implies(vacations[i] == "beach", house_styles[i] == "ranch"))

    # Clue 10: colonial and camping have one house between
    for i in range(6):
        for j in range(6):
            s.add(z3.Implies(z3.And(house_styles[i] == "colonial", vacations[j] == "camping"), z3.Or(j == i + 2, i == j + 2)))

    # Clue 11: mountain vacation is yellow monster
    for i in range(6):
        s.add(z3.Implies(vacations[i] == "mountain", cigars[i] == "yellow monster"))

    # Clue 12: mountain is very tall
    for i in range(6):
        s.add(z3.Implies(vacations[i] == "mountain", heights[i] == "very tall"))

    # Clue 13: mountain and Dunhill next to each other
    for i in range(6):
        cond = vacations[i] == "mountain"
        clauses = []
        if i < 5:
            clauses.append(cigars[i+1] == "dunhill")
        if i > 0:
            clauses.append(cigars[i-1] == "dunhill")
        if clauses:
            s.add(z3.Implies(cond, z3.Or(clauses)))

    # Clue 14: spaghetti is in Victorian
    s.add(house_styles[4] == "victorian")

    # Clue 15: tall is beach
    for i in range(6):
        s.add(z3.Implies(heights[i] == "tall", vacations[i] == "beach"))

    # Clue 16: tall is left of Victorian (index 4)
    for i in range(6):
        s.add(z3.Implies(heights[i] == "tall", i < 4))

    # Clue 18: modern is left of Alice (index 4)
    for i in range(6):
        s.add(z3.Implies(house_styles[i] == "modern", i < 4))

    # Clue 19: Craftsman left of short
    for i in range(6):
        cond = house_styles[i] == "craftsman"
        clauses = [heights[j] == "short" for j in range(i+1, 6)]
        if clauses:
            s.add(z3.Implies(cond, z3.Or(clauses)))

    # Clue 20: stir fry left of Prince
    for i in range(6):
        for j in range(6):
            s.add(z3.Implies(z3.And(foods[i] == "stir fry", cigars[j] == "prince"), i < j))

    # Clue 21: grilled cheese and super tall have two houses between
    for i in range(6):
        for j in range(6):
            s.add(z3.Implies(z3.And(foods[i] == "grilled cheese", heights[j] == "super tall"), z3.Or(j == i + 3, i == j + 3)))

    # Clue 22: ranch is blue master
    for i in range(6):
        s.add(z3.Implies(house_styles[i] == "ranch", cigars[i] == "blue master"))

    # Clue 23: blends left of blue master
    for i in range(5):  # i can be 0-4
        s.add(z3.Implies(cigars[i] == "blends", cigars[i+1] == "blue master"))

    # Clue 24: cultural is pizza
    for i in range(6):
        s.add(z3.Implies(vacations[i] == "cultural", foods[i] == "pizza"))

    # Clue 25: pizza left of cruise
    for i in range(6):
        for j in range(6):
            s.add(z3.Implies(z3.And(foods[i] == "pizza", vacations[j] == "cruise"), i < j))

    # Check if the constraints are satisfiable
    if s.check() == z3.sat:
        model = s.model()
        # Extract the solution
        solution = []
        for i in range(6):
            house_num = str(i + 1)
            name_val = model[names[i]].as_string()
            house_style_val = model[house_styles[i]].as_string()
            food_val = model[foods[i]].as_string()
            vacation_val = model[vacations[i]].as_string()
            height_val = model[heights[i]].as_string()
            cigar_val = model[cigars[i]].as_string()
            solution.append([house_num, name_val, house_style_val, food_val, vacation_val, height_val, cigar_val])
        # Return the JSON structure
        return {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                "rows": solution
            }
    else:
        return "No solution found."

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))