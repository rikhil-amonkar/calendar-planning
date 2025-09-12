from z3 import *
import json

def main():
    # Define the sorts for each attribute
    Name, (Arnold, Peter, Eric, Alice, Bob) = EnumSort('Name', ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob'])
    Hobby, (painting, cooking, knitting, gardening, photography) = EnumSort('Hobby', ['painting', 'cooking', 'knitting', 'gardening', 'photography'])
    Height, (very_tall, tall, very_short, average, short) = EnumSort('Height', ['very tall', 'tall', 'very short', 'average', 'short'])
    Food, (stew, grilled_cheese, stir_fry, spaghetti, pizza) = EnumSort('Food', ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza'])

    # Create variables for each house
    houses = range(1, 6)
    n = [Const(f'n_{i}', Name) for i in houses]
    hb = [Const(f'hb_{i}', Hobby) for i in houses]
    ht = [Const(f'ht_{i}', Height) for i in houses]
    f = [Const(f'f_{i}', Food) for i in houses]

    s = Solver()

    # All attributes are distinct
    s.add(Distinct(n))
    s.add(Distinct(hb))
    s.add(Distinct(ht))
    s.add(Distinct(f))

    # Clue 1: Bob is the photography enthusiast.
    for i in range(5):
        s.add(Implies(n[i] == Bob, hb[i] == photography))

    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    for i in range(5):
        s.add(Implies(f[i] == grilled_cheese, ht[i] == tall))
        s.add(Implies(ht[i] == tall, f[i] == grilled_cheese))

    # Clue 3: Peter is not in the second house.
    s.add(n[1] != Peter)

    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    # Since clue 13 places tall in third house, we handle it there.

    # Clue 5: The person who loves cooking is the person who has an average height.
    for i in range(5):
        s.add(Implies(hb[i] == cooking, ht[i] == average))
        s.add(Implies(ht[i] == average, hb[i] == cooking))

    # Clue 6: Alice is directly left of the person who is a pizza lover.
    for i in range(4):
        s.add(Implies(n[i] == Alice, f[i+1] == pizza))

    # Clue 7: The person who loves the spaghetti eater is not in the second house.
    s.add(f[1] != spaghetti)

    # Clue 8: Eric is not in the fifth house.
    s.add(n[4] != Eric)

    # Clue 9: The person who is short is Peter.
    for i in range(5):
        s.add(Implies(ht[i] == short, n[i] == Peter))
        s.add(Implies(n[i] == Peter, ht[i] == short))

    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    for i in range(4):
        s.add(Or(
            And(ht[i] == average, hb[i+1] == gardening),
            And(ht[i+1] == average, hb[i] == gardening),
            And(ht[i] == average, hb[i] == gardening),  # Same house case
            And(ht[i+1] == average, hb[i+1] == gardening)  # Same house case
        ))

    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    for i in range(4):
        s.add(Implies(hb[i] == painting, f[i+1] == grilled_cheese))

    # Clue 12: The person who is very short is in the fifth house.
    s.add(ht[4] == very_short)

    # Clue 13: The person who is tall is in the third house.
    s.add(ht[2] == tall)
    # From clue 4 and 13: tall is in house 3, so stir fry is in house 4
    s.add(f[3] == stir_fry)

    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    # Since Bob is photography enthusiast (clue 1), Alice is right of Bob
    bob_index = Int('bob_index')
    alice_index = Int('alice_index')
    s.add(bob_index >= 0, bob_index <= 4)
    s.add(alice_index >= 0, alice_index <= 4)
    for i in range(5):
        s.add(If(n[i] == Bob, bob_index == i, True))
        s.add(If(n[i] == Alice, alice_index == i, True))
    s.add(alice_index > bob_index)

    # Check and get model
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(5):
            name_val = m.evaluate(n[i])
            hobby_val = m.evaluate(hb[i])
            height_val = m.evaluate(ht[i])
            food_val = m.evaluate(f[i])
            result.append([
                str(i+1),
                str(name_val),
                str(hobby_val),
                str(height_val),
                str(food_val)
            ])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Height", "Food"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()