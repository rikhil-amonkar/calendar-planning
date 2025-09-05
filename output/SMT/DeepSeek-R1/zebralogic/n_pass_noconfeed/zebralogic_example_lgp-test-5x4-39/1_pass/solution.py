import json
from z3 import *

def main():
    # Define the sorts for each attribute
    NameSort, (Arnold, Peter, Eric, Alice, Bob) = EnumSort('NameSort', ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob'])
    HobbySort, (painting, cooking, knitting, gardening, photography) = EnumSort('HobbySort', ['painting', 'cooking', 'knitting', 'gardening', 'photography'])
    HeightSort, (very_tall, tall, very_short, average, short) = EnumSort('HeightSort', ['very tall', 'tall', 'very short', 'average', 'short'])
    FoodSort, (stew, grilled_cheese, stir_fry, spaghetti, pizza) = EnumSort('FoodSort', ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza'])

    # Create arrays for each attribute for the 5 houses
    names = [Const(f'name_{i}', NameSort) for i in range(5)]
    hobbies = [Const(f'hobby_{i}', HobbySort) for i in range(5)]
    heights = [Const(f'height_{i}', HeightSort) for i in range(5)]
    foods = [Const(f'food_{i}', FoodSort) for i in range(5)]

    s = Solver()

    # Assert all attributes are distinct
    s.add(Distinct(names))
    s.add(Distinct(hobbies))
    s.add(Distinct(heights))
    s.add(Distinct(foods))

    # Clue 1: Bob is the photography enthusiast.
    for i in range(5):
        s.add(Implies(hobbies[i] == photography, names[i] == Bob))

    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    for i in range(5):
        s.add(Implies(foods[i] == grilled_cheese, heights[i] == tall))

    # Clue 3: Peter is not in the second house.
    s.add(names[1] != Peter)

    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    for i in range(4):
        s.add(Implies(heights[i] == tall, foods[i+1] == stir_fry))

    # Clue 5: The person who loves cooking is the person who has an average height.
    for i in range(5):
        s.add(Implies(hobbies[i] == cooking, heights[i] == average))

    # Clue 6: Alice is directly left of the person who is a pizza lover.
    for i in range(4):
        s.add(Implies(names[i] == Alice, foods[i+1] == pizza))

    # Clue 7: The person who loves the spaghetti eater is not in the second house.
    s.add(foods[1] != spaghetti)

    # Clue 8: Eric is not in the fifth house.
    s.add(names[4] != Eric)

    # Clue 9: The person who is short is Peter.
    for i in range(5):
        s.add(Implies(heights[i] == short, names[i] == Peter))

    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    adjacent_constraints = []
    for i in range(4):
        adjacent_constraints.append(Or(
            And(heights[i] == average, hobbies[i+1] == gardening),
            And(heights[i+1] == average, hobbies[i] == gardening)
        ))
    s.add(Or(adjacent_constraints))

    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    for i in range(4):
        s.add(Implies(hobbies[i] == painting, foods[i+1] == grilled_cheese))

    # Clue 12: The person who is very short is in the fifth house.
    s.add(heights[4] == very_short)

    # Clue 13: The person who is tall is in the third house.
    s.add(heights[2] == tall)

    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    photo_index = Int('photo_index')
    alice_index = Int('alice_index')
    s.add(And(photo_index >= 0, photo_index < 5))
    s.add(And(alice_index >= 0, alice_index < 5))
    for i in range(5):
        s.add(Implies(hobbies[i] == photography, photo_index == i))
        s.add(Implies(names[i] == Alice, alice_index == i))
    s.add(alice_index > photo_index)

    # Check for a solution
    if s.check() != sat:
        print("No solution found")
        return

    m = s.model()
    rows = []
    for i in range(5):
        n_val = m.eval(names[i])
        hb_val = m.eval(hobbies[i])
        ht_val = m.eval(heights[i])
        f_val = m.eval(foods[i])
        rows.append([str(i+1), str(n_val), str(hb_val), str(ht_val), str(f_val)])

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()