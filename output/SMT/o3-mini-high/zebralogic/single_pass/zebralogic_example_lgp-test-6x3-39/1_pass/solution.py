from z3 import *

def main():
    s_solver = Solver()

    # We have 6 houses (indexed 0 to 5 corresponding to houses 1 to 6)
    # In each house there is a mother, her child, and her favorite smoothie.
    # We assign each attribute an integer value as follows:
    #
    # Mothers (names):
    #   0: Arnold
    #   1: Peter
    #   2: Carol
    #   3: Alice
    #   4: Bob
    #   5: Eric
    #
    # Children:
    #   0: Alice
    #   1: Timothy
    #   2: Bella
    #   3: Meredith
    #   4: Fred
    #   5: Samantha
    #
    # Smoothies:
    #   0: desert
    #   1: cherry
    #   2: watermelon
    #   3: blueberry
    #   4: lime
    #   5: dragonfruit

    num_houses = 6

    # Create an array for each attribute: m for mothers, c for children, s for smoothies.
    m = [Int(f"m_{i}") for i in range(num_houses)]
    c = [Int(f"c_{i}") for i in range(num_houses)]
    s = [Int(f"s_{i}") for i in range(num_houses)]

    # Domain constraints: each value is between 0 and 5.
    for i in range(num_houses):
        s_solver.add(And(m[i] >= 0, m[i] < 6))
        s_solver.add(And(c[i] >= 0, c[i] < 6))
        s_solver.add(And(s[i] >= 0, s[i] < 6))
    
    # All values in each category must be distinct.
    s_solver.add(Distinct(m))
    s_solver.add(Distinct(c))
    s_solver.add(Distinct(s))

    # Clue 1:
    # "The person's child is named Fred and the Desert smoothie lover are next to each other."
    # If a house has child Fred (child value 4), then at least one neighbor must have smoothie desert (0).
    for i in range(num_houses):
        s_solver.add(Implies(c[i] == 4,
                             Or(And(i > 0, s[i-1] == 0),
                                And(i < num_houses - 1, s[i+1] == 0))))

    # Clue 2:
    # "The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred."
    # Blueberry smoothie value is 3; child Fred is 4.
    for i in range(num_houses):
        for j in range(num_houses):
            s_solver.add(Implies(And(s[i] == 3, c[j] == 4), i < j))

    # Clue 3:
    # "Alice is not in the fifth house."
    # Mother Alice is value 3; the fifth house is index 4.
    s_solver.add(m[4] != 3)

    # Clue 4:
    # "The person's child is named Samantha is not in the second house."
    # Child Samantha is value 5; the second house is index 1.
    s_solver.add(c[1] != 5)

    # Clue 5:
    # "The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies."
    # Watermelon is 2; Cherry is 1.
    for i in range(num_houses):
        for j in range(num_houses):
            s_solver.add(Implies(And(s[i] == 1, s[j] == 2), i < j))

    # Clue 6:
    # "Alice is the person's child is named Alice."
    # This tells us that the mother named Alice (3) has child Alice (0). (We make it bidirectional.)
    for i in range(num_houses):
        s_solver.add(Implies(m[i] == 3, c[i] == 0))
        s_solver.add(Implies(c[i] == 0, m[i] == 3))

    # Clue 7:
    # "Alice is the Watermelon smoothie lover."
    # So the house with mother Alice (3) must have smoothie watermelon (2). (Enforced in both directions.)
    for i in range(num_houses):
        s_solver.add(Implies(m[i] == 3, s[i] == 2))
        s_solver.add(Implies(s[i] == 2, m[i] == 3))

    # Clue 8:
    # "Peter is somewhere to the right of the person's child is named Samantha."
    # Peter is 1; Samantha (child) is 5.
    for i in range(num_houses):
        for j in range(num_houses):
            s_solver.add(Implies(And(c[i] == 5, m[j] == 1), i < j))

    # Clue 9:
    # "Arnold is not in the second house."
    # Arnold is 0; second house is index 1.
    s_solver.add(m[1] != 0)

    # Clue 10:
    # "Bob is the person who is the mother of Timothy."
    # Bob is 4; Timothy (child) is 1. (Again, we add bidirectional equalities.)
    for i in range(num_houses):
        s_solver.add(Implies(m[i] == 4, c[i] == 1))
        s_solver.add(Implies(c[i] == 1, m[i] == 4))

    # Clue 11:
    # "Arnold is directly left of Carol."
    # Arnold is 0; Carol is 2.
    for i in range(num_houses):
        s_solver.add(Implies(m[i] == 0, And(i < num_houses - 1, m[i+1] == 2)))
    for i in range(1, num_houses):
        s_solver.add(Implies(m[i] == 2, m[i-1] == 0))

    # Clue 12:
    # "The person who likes Cherry smoothies is directly left of the person's child is named Samantha."
    # Cherry smoothie is 1; child Samantha is 5.
    for i in range(num_houses):
        s_solver.add(Implies(s[i] == 1, And(i < num_houses - 1, c[i+1] == 5)))
    for i in range(1, num_houses):
        s_solver.add(Implies(c[i] == 5, s[i-1] == 1))

    # Clue 13:
    # "The person's child is named Meredith is in the sixth house."
    # Meredith is 3 and the sixth house is index 5.
    s_solver.add(c[5] == 3)

    # Clue 14:
    # "The Dragonfruit smoothie lover is the person's child is named Meredith."
    # Dragonfruit is 5. Since the only house with child Meredith (3) is house 6, we set its smoothie.
    s_solver.add(s[5] == 5)

    # At this point, the remaining unassigned values will be fixed by distinctness.
    # Our intended solution (if the Z3 model is found) is:
    # House 1: m = Arnold (0),       c = Bella (2),      s = blueberry (3)
    # House 2: m = Carol (2),         c = Fred (4),       s = cherry (1)
    # House 3: m = Eric (5),          c = Samantha (5),   s = desert (0)
    # House 4: m = Alice (3),         c = Alice (0),      s = watermelon (2)
    # House 5: m = Bob (4),           c = Timothy (1),    s = lime (4)
    # House 6: m = Peter (1),         c = Meredith (3),   s = dragonfruit (5)

    if s_solver.check() == sat:
        model = s_solver.model()
        # Reverse maps to turn integer values back to strings.
        mothers = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
        children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
        smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

        solution = {"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": []}}
        for i in range(num_houses):
            house_no = str(i + 1)
            m_val = mothers[model[m[i]].as_long()]
            c_val = children[model[c[i]].as_long()]
            s_val = smoothies[model[s[i]].as_long()]
            solution["solution"]["rows"].append([house_no, m_val, c_val, s_val])
        
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()