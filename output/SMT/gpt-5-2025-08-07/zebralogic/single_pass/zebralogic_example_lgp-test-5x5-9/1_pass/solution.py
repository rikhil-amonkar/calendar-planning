import json
from z3 import Solver, IntVector, Distinct, And, Or, Implies

def iff(a, b):
    return And(Implies(a, b), Implies(b, a))

def solve_puzzle():
    N = 5  # 5 houses, indexed 0..4

    # Attribute domains encoded as 0..4
    names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks = ["milk", "root beer", "coffee", "tea", "water"]
    colors = ["blue", "green", "white", "yellow", "red"]
    flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

    # Create variables per house for each attribute
    name = IntVector('name', N)
    drink = IntVector('drink', N)
    color = IntVector('color', N)
    flower = IntVector('flower', N)
    hobby = IntVector('hobby', N)

    s = Solver()

    # Domain constraints and all-different for each attribute
    for arr in [name, drink, color, flower, hobby]:
        for v in arr:
            s.add(v >= 0, v < N)
        s.add(Distinct(arr))

    # Index constants for readability
    N_BOB, N_ARNOLD, N_PETER, N_ALICE, N_ERIC = range(5)
    DR_MILK, DR_ROOT_BEER, DR_COFFEE, DR_TEA, DR_WATER = range(5)
    C_BLUE, C_GREEN, C_WHITE, C_YELLOW, C_RED = range(5)
    F_DAFFODILS, F_ROSES, F_LILIES, F_TULIPS, F_CARNATIONS = range(5)
    H_PAINTING, H_COOKING, H_PHOTOGRAPHY, H_GARDENING, H_KNITTING = range(5)

    # Clues:

    # 1. Alice is not in the fourth house. (4th house is index 3)
    s.add(name[3] != N_ALICE)

    # 2. The root beer lover is the person who enjoys gardening.
    for i in range(N):
        s.add(iff(drink[i] == DR_ROOT_BEER, hobby[i] == H_GARDENING))

    # 3. The person whose favorite color is green is the coffee drinker.
    for i in range(N):
        s.add(iff(color[i] == C_GREEN, drink[i] == DR_COFFEE))

    # 4. The person whose favorite color is green is the person who loves the bouquet of lilies.
    for i in range(N):
        s.add(iff(color[i] == C_GREEN, flower[i] == F_LILIES))

    # 5. The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
    s.add(Or([And(i < j, flower[i] == F_DAFFODILS, color[j] == C_BLUE) for i in range(N) for j in range(N) if i < j]))

    # 6. The person who loves cooking is the person who loves blue.
    for i in range(N):
        s.add(iff(hobby[i] == H_COOKING, color[i] == C_BLUE))

    # 7. Eric is directly left of the tea drinker.
    s.add(Or([And(name[i] == N_ERIC, drink[i + 1] == DR_TEA) for i in range(N - 1)]))

    # 8. The one who only drinks water is Peter.
    for i in range(N):
        s.add(iff(drink[i] == DR_WATER, name[i] == N_PETER))

    # 9. Arnold is the photography enthusiast.
    for i in range(N):
        s.add(iff(name[i] == N_ARNOLD, hobby[i] == H_PHOTOGRAPHY))

    # 10. The person who loves white is the person who loves the rose bouquet.
    for i in range(N):
        s.add(iff(color[i] == C_WHITE, flower[i] == F_ROSES))

    # 11. There is one house between carnations and red.
    s.add(Or(
        *[And(flower[i] == F_CARNATIONS, color[i + 2] == C_RED) for i in range(N - 2)],
        *[And(color[i] == C_RED, flower[i + 2] == F_CARNATIONS) for i in range(N - 2)]
    ))

    # 12. Cooking is somewhere to the left of painting.
    s.add(Or([And(i < j, hobby[i] == H_COOKING, hobby[j] == H_PAINTING) for i in range(N) for j in range(N) if i < j]))

    # 13. The one who only drinks water is in the third house. (index 2)
    s.add(drink[2] == DR_WATER)

    # 14. The person who loves a carnations arrangement is the root beer lover.
    for i in range(N):
        s.add(iff(flower[i] == F_CARNATIONS, drink[i] == DR_ROOT_BEER))

    # 15. The person who loves white is in the second house. (index 1)
    s.add(color[1] == C_WHITE)

    if s.check().r == 1:  # sat
        m = s.model()

        result_rows = []
        for i in range(N):
            row = [
                str(i + 1),
                names[m[name[i]].as_long()],
                drinks[m[drink[i]].as_long()],
                colors[m[color[i]].as_long()],
                flowers[m[flower[i]].as_long()],
                hobbies[m[hobby[i]].as_long()],
            ]
            result_rows.append(row)

        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                "rows": result_rows
            }
        }
        print(json.dumps(output, ensure_ascii=False))
    else:
        # In the unlikely case of unsat, still output valid structure with empty rows
        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()