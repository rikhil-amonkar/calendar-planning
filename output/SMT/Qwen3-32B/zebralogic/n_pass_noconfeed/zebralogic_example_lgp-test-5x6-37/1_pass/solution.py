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
        solver.add(If(height[i] == Average, child[i] == Meredith, True))

    # Clue 2: Tall is in house 2
    solver.add(height[2] == Tall)

    # Clue 3: Peter is directly left of the person residing in a Victorian house
    clue3 = Or([And(name[i] == Peter, house_style[i+1] == Victorian) for i in range(1, 5)])
    solver.add(clue3)

    # Clue 4: Alice is the person who is tall
    solver.add(name[2] == Alice)

    # Clue 5: The person who loves baseball is the person who is very tall
    for i in houses:
        solver.add(If(sport[i] == Baseball, height[i] == VeryTall, True))
        solver.add(If(height[i] == VeryTall, sport[i] == Baseball, True))

    # Clue 6: Meredith's parent and Timothy's parent are next to each other
    clue6 = Or([Or(And(child[i] == Meredith, child[i+1] == Timothy), And(child[i+1] == Meredith, child[i] == Timothy)) for i in range(1, 5)])
    solver.add(clue6)

    # Clue 7: Bob's hobby is painting
    for i in houses:
        solver.add(If(name[i] == Bob, hobby[i] == Painting, True))

    # Clue 8: Gardening is in house 2
    solver.add(hobby[2] == Gardening)

    # Clue 9: VeryShort is to the right of Eric
    for j in range(2, 6):
        i_values = range(1, j)
        condition = Or([name[i] == Eric for i in i_values])
        solver.add(If(height[j] == VeryShort, condition, True))
    solver.add(height[1] != VeryShort)

    # Clue 10: Tennis lover has child Samantha
    for i in houses:
        solver.add(If(sport[i] == Tennis, child[i] == Samantha, True))

    # Clue 11: Soccer not in first house
    for i in houses:
        solver.add(If(sport[i] == Soccer, i != 1, True))

    # Clue 12: Samantha's parent is in modern-style house
    for i in houses:
        solver.add(If(child[i] == Samantha, house_style[i] == Modern, True))

    # Clue 13: Craftsman style has average height
    for i in houses:
        solver.add(If(house_style[i] == Craftsman, height[i] == Average, True))

    # Clue 14: Fred's parent is in Victorian house
    for i in houses:
        solver.add(If(child[i] == Fred, house_style[i] == Victorian, True))

    # Clue 15: Short person loves basketball
    for i in houses:
        solver.add(If(height[i] == Short, sport[i] == Basketball, True))

    # Clue 16: Peter is very tall
    for i in houses:
        solver.add(If(name[i] == Peter, height[i] == VeryTall, True))

    # Clue 17: Ranch is left of cooking
    clue17 = Or([And(house_style[i] == Ranch, hobby[j] == Cooking) for i in range(1, 5) for j in range(i+1, 6)])
    solver.add(clue17)

    # Clue 18: Knitting and Gardening are adjacent
    solver.add(Or(hobby[1] == Knitting, hobby[3] == Knitting))

    # Clue 19: Modern style has cooking
    for i in houses:
        solver.add(If(house_style[i] == Modern, hobby[i] == Cooking, True))

    # Clue 20: Victorian is in house 5
    solver.add(house_style[5] == Victorian)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in houses:
            row = [
                str(i),
                model.evaluate(name[i]).decl().name(),
                model.evaluate(hobby[i]).decl().name(),
                model.evaluate(sport[i]).decl().name(),
                model.evaluate(house_style[i]).decl().name(),
                model.evaluate(child[i]).decl().name(),
                model.evaluate(height[i]).decl().name()
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