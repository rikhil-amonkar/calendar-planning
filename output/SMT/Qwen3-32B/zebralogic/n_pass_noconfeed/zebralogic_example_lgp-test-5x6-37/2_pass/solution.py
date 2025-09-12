from z3 import *
import json

def main():
    # Define EnumSorts
    Name, (Bob, Arnold, Alice, Peter, Eric) = EnumSort('Name', ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric'])
    Hobby, (Cooking, Gardening, Painting, Photography, Knitting) = EnumSort('Hobby', ['cooking', 'gardening', 'painting', 'photography', 'knitting'])
    Sport, (Swimming, Tennis, Soccer, Baseball, Basketball) = EnumSort('Sport', ['swimming', 'tennis', 'soccer', 'baseball', 'basketball'])
    HouseStyle, (Ranch, Craftsman, Victorian, Modern, Colonial) = EnumSort('HouseStyle', ['ranch', 'craftsman', 'victorian', 'modern', 'colonial'])
    Child, (Timothy, Samantha, Bella, Meredith, Fred) = EnumSort('Child', ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred'])
    Height, (Average, VeryTall, VeryShort, Short, Tall) = EnumSort('Height', ['average', 'very tall', 'very short', 'short', 'tall'])

    # Create variables for each house (1-5) and each attribute
    houses = [1, 2, 3, 4, 5]
    name = [Const(f"name_{i}", Name) for i in houses]
    hobby = [Const(f"hobby_{i}", Hobby) for i in houses]
    sport = [Const(f"sport_{i}", Sport) for i in houses]
    house_style = [Const(f"style_{i}", HouseStyle) for i in houses]
    child = [Const(f"child_{i}", Child) for i in houses]
    height = [Const(f"height_{i}", Height) for i in houses]

    solver = Solver()

    # Add constraints that each attribute is unique per category
    for lst in [name, hobby, sport, house_style, child, height]:
        solver.add(Distinct(lst))

    # Now add all the clues as constraints

    # Clue 1: The person with average height has child Meredith.
    for i in houses:
        solver.add(If(height[i-1] == Average, child[i-1] == Meredith, True))

    # Clue 2: Tall is in house 2
    solver.add(height[1] == Tall)

    # Clue 3: Peter is directly left of the person residing in a Victorian house
    clue3 = Or([And(name[i-1] == Peter, house_style[i] == Victorian) for i in range(1, 5)])
    solver.add(clue3)

    # Clue 4: Alice is the person who is tall
    solver.add(name[1] == Alice)

    # Clue 5: The person who loves baseball is the person who is very tall
    for i in houses:
        solver.add(If(sport[i-1] == Baseball, height[i-1] == VeryTall, True))
        solver.add(If(height[i-1] == VeryTall, sport[i-1] == Baseball, True))

    # Clue 6: Meredith's parent and Timothy's parent are next to each other
    clue6 = Or([Or(And(child[i-1] == Meredith, child[i] == Timothy), And(child[i] == Meredith, child[i-1] == Timothy)) for i in range(1, 5)])
    solver.add(clue6)

    # Clue 7: Bob's hobby is painting
    for i in houses:
        solver.add(If(name[i-1] == Bob, hobby[i-1] == Painting, True))

    # Clue 8: Gardening is in house 2
    solver.add(hobby[1] == Gardening)

    # Clue 9: VeryShort is to the right of Eric
    for j in range(2, 6):
        i_values = range(1, j)
        condition = Or([name[i-1] == Eric for i in i_values])
        solver.add(If(height[j-1] == VeryShort, condition, True))
    solver.add(height[0] != VeryShort)

    # Clue 10: Tennis lover has child Samantha
    for i in houses:
        solver.add(If(sport[i-1] == Tennis, child[i-1] == Samantha, True))

    # Clue 11: Soccer not in first house
    for i in houses:
        solver.add(If(sport[i-1] == Soccer, i != 1, True))

    # Clue 12: Samantha's parent is in modern-style house
    for i in houses:
        solver.add(If(child[i-1] == Samantha, house_style[i-1] == Modern, True))

    # Clue 13: Craftsman style has average height
    for i in houses:
        solver.add(If(house_style[i-1] == Craftsman, height[i-1] == Average, True))

    # Clue 14: Fred's parent is in Victorian house
    for i in houses:
        solver.add(If(child[i-1] == Fred, house_style[i-1] == Victorian, True))

    # Clue 15: Short person loves basketball
    for i in houses:
        solver.add(If(height[i-1] == Short, sport[i-1] == Basketball, True))

    # Clue 16: Peter is very tall
    for i in houses:
        solver.add(If(name[i-1] == Peter, height[i-1] == VeryTall, True))

    # Clue 17: Ranch is left of cooking
    clue17 = Or([And(house_style[i-1] == Ranch, hobby[j-1] == Cooking) for i in range(1, 5) for j in range(i+1, 6)])
    solver.add(clue17)

    # Clue 18: Knitting and Gardening are adjacent
    solver.add(Or(hobby[0] == Knitting, hobby[2] == Knitting))

    # Clue 19: Modern style has cooking
    for i in houses:
        solver.add(If(house_style[i-1] == Modern, hobby[i-1] == Cooking, True))

    # Clue 20: Victorian is in house 5
    solver.add(house_style[4] == Victorian)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in houses:
            idx = i - 1
            row = [
                str(i),
                model.evaluate(name[idx]).decl().name(),
                model.evaluate(hobby[idx]).decl().name(),
                model.evaluate(sport[idx]).decl().name(),
                model.evaluate(house_style[idx]).decl().name(),
                model.evaluate(child[idx]).decl().name(),
                model.evaluate(height[idx]).decl().name()
            ]
            solution.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                "rows": solution
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()