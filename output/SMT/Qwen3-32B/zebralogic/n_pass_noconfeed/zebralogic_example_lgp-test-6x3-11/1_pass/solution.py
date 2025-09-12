from z3 import *
import json

def main():
    # Define variables for each house (0-based index)
    name = [Int(f'name_{i}') for i in range(6)]
    haircolor = [Int(f'haircolor_{i}') for i in range(6)]
    height = [Int(f'height_{i}') for i in range(6)]

    s = Solver()

    # Each attribute must be a permutation of 0-5
    for attr in [name, haircolor, height]:
        s.add(Distinct(attr))
        s.add([And(0 <= attr[i], attr[i] <= 5) for i in range(6)])

    # Clue 2: Alice is in the fourth house (index 3)
    s.add(name[3] == 3)

    # Clue 4: The person who is tall is in the sixth house (index 5)
    s.add(height[5] == 3)

    # Clue 10: The person who is very short is in the fifth house (index 4)
    s.add(height[4] == 2)

    # Clue 12: The person who has gray hair is in the third house (index 2)
    s.add(haircolor[2] == 5)

    # Clue 5: The person who has black hair is not in the fourth house (index 3)
    s.add(haircolor[3] != 3)

    # Clue 1: The person who has blonde hair is directly left of Bob
    s.add(Or([And(haircolor[i] == 1, name[i+1] == 0) for i in range(5)]))

    # Clue 3: The person who is short is Arnold
    s.add(Or([And(height[i] == 5, name[i] == 4) for i in range(6)]))

    # Clue 6: The person who has red hair is Eric
    s.add(Or([And(haircolor[i] == 4, name[i] == 2) for i in range(6)]))

    # Clue 7: The person who is super tall is to the right of average height
    s.add(Or([And(height[j] == 1, height[i] == 4) for j in range(6) for i in range(j+1, 6)]))

    # Clue 8: The person who has blonde hair is Carol
    s.add(Or([And(haircolor[i] == 1, name[i] == 5) for i in range(6)]))

    # Clue 9: One house between gray and red hair
    s.add(Or(haircolor[0] == 4, haircolor[4] == 4))

    # Clue 11: Bob has brown hair
    s.add(Or([And(name[i] == 0, haircolor[i] == 2) for i in range(6)]))

    # Clue 13: The person with blonde hair is very tall
    s.add(Or([And(haircolor[i] == 1, height[i] == 0) for i in range(6)]))

    if s.check() == sat:
        model = s.model()
        names_list = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
        haircolors_list = ["auburn", "blonde", "brown", "black", "red", "gray"]
        heights_list = ["very tall", "average", "very short", "tall", "super tall", "short"]

        rows = []
        for i in range(6):
            n = model.eval(name[i]).as_long()
            h_c = model.eval(haircolor[i]).as_long()
            h = model.eval(height[i]).as_long()
            house_num = i + 1
            rows.append([
                str(house_num),
                names_list[n],
                haircolors_list[h_c],
                heights_list[h]
            ])

        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()