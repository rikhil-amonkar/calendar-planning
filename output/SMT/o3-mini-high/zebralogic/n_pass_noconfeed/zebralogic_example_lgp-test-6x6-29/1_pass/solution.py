from z3 import *
import json

def main():
    # There are 6 houses, with indices 0 to 5 (House number = index+1)
    num_houses = 6

    # Attributes: using integers 0..5
    # Names: 0: Arnold, 1: Carol, 2: Peter, 3: Eric, 4: Bob, 5: Alice
    # HouseStyle: 0: ranch, 1: colonial, 2: modern, 3: craftsman, 4: mediterranean, 5: victorian
    # Food: 0: pizza, 1: stew, 2: spaghetti, 3: grilled cheese, 4: stir fry, 5: soup
    # Vacation: 0: cultural, 1: cruise, 2: mountain, 3: camping, 4: city, 5: beach
    # Height: 0: average, 1: very tall, 2: very short, 3: short, 4: tall, 5: super tall
    # Cigar: 0: yellow monster, 1: prince, 2: dunhill, 3: pall mall, 4: blue master, 5: blends

    names_enum = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    styles_enum = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods_enum = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations_enum = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights_enum = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars_enum = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

    # Create variables for each house and attribute.
    N = [Int(f"name_{i}") for i in range(num_houses)]
    S = [Int(f"style_{i}") for i in range(num_houses)]
    F = [Int(f"food_{i}") for i in range(num_houses)]
    V = [Int(f"vacation_{i}") for i in range(num_houses)]
    H = [Int(f"height_{i}") for i in range(num_houses)]
    C = [Int(f"cigar_{i}") for i in range(num_houses)]
    
    solver = Solver()

    # Each attribute for each house is in range 0..5
    for lst in [N, S, F, V, H, C]:
        for var in lst:
            solver.add(var >= 0, var < num_houses)

    # All attributes are a permutation: they are all different.
    solver.add(Distinct(N))
    solver.add(Distinct(S))
    solver.add(Distinct(F))
    solver.add(Distinct(V))
    solver.add(Distinct(H))
    solver.add(Distinct(C))

    # Clue 1: Alice is in the fifth house.
    # House 5 is index 4.
    solver.add(N[4] == 5)

    # Clue 2: The person who loves stir fry (food==4) is the person living in a colonial-style house (style==1).
    for i in range(num_houses):
        solver.add(Implies(F[i] == 4, S[i] == 1))

    # Clue 3: Alice is the person who loves the spaghetti eater (interpreted as: Alice eats spaghetti, food==2).
    for i in range(num_houses):
        solver.add(Implies(N[i] == 5, F[i] == 2))

    # Clue 4: Arnold is the person who loves the stew (stew food==1).
    for i in range(num_houses):
        solver.add(Implies(N[i] == 0, F[i] == 1))

    # Clue 5: There is one house between the person who has an average height (height==0) and Peter (name==2).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(H[i] == 0, N[j] == 2), Or(i == j + 2, i == j - 2)))

    # Clue 6: The person in a Craftsman-style house (style==3) is not in the third house (index 2).
    solver.add(S[2] != 3)

    # Clue 7: The person who has an average height (height==0) is the person who loves stir fry (food==4).
    for i in range(num_houses):
        solver.add(Implies(H[i] == 0, F[i] == 4))

    # Clue 8: The person who enjoys beach vacations (vacation==5) is the person in a ranch-style home (style==0).
    for i in range(num_houses):
        solver.add(Implies(V[i] == 5, S[i] == 0))
        solver.add(Implies(S[i] == 0, V[i] == 5))

    # Clue 9: Eric is in the fourth house (index 3).
    solver.add(N[3] == 3)

    # Clue 10: There is one house between the person living in a colonial-style house (style==1) and the person who enjoys camping trips (vacation==3).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(S[i] == 1, V[j] == 3), Or(i == j + 2, i == j - 2)))

    # Clue 11: The person who enjoys mountain retreats (vacation==2) is the person who smokes Yellow Monster (cigar==0).
    for i in range(num_houses):
        solver.add(Implies(V[i] == 2, C[i] == 0))
        solver.add(Implies(C[i] == 0, V[i] == 2))

    # Clue 12: The person who enjoys mountain retreats (vacation==2) is the person who is very tall (height==1).
    for i in range(num_houses):
        solver.add(Implies(V[i] == 2, H[i] == 1))
        solver.add(Implies(H[i] == 1, V[i] == 2))

    # Clue 13: The person who enjoys mountain retreats (vacation==2) and the Dunhill smoker (cigar==2) are next to each other.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(V[i] == 2, C[j] == 2), Abs(i - j) == 1))

    # Clue 14: The person who loves the spaghetti eater (spaghetti food==2) is the person residing in a Victorian house (style==5).
    for i in range(num_houses):
        solver.add(Implies(F[i] == 2, S[i] == 5))
        solver.add(Implies(S[i] == 5, F[i] == 2))

    # Clue 15: The person who is tall (height==4) is the person who loves beach vacations (vacation==5).
    for i in range(num_houses):
        solver.add(Implies(H[i] == 4, V[i] == 5))
        solver.add(Implies(V[i] == 5, H[i] == 4))

    # Clue 16: The person who is tall (height==4) is somewhere to the left of the person residing in a Victorian house (style==5).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(H[i] == 4, S[j] == 5), i < j))
    
    # Clue 17: The person who loves stir fry (food==4) is directly left of Bob (name==4).
    for i in range(num_houses - 1):
        solver.add(Implies(F[i] == 4, N[i+1] == 4))
    # Also, stir fry cannot be in the last house.
    solver.add(F[num_houses - 1] != 4)

    # Clue 18: The person in a modern-style house (style==2) is somewhere to the left of Alice (name==5).
    # Since we know Alice is in the fifth house (index 4), at least one house among 0...3 must be modern.
    solver.add(Or([S[i] == 2 for i in range(4)]))

    # Clue 19: The person in a Craftsman-style house (style==3) is somewhere to the left of the person who is short (height==3).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(S[i] == 3, H[j] == 3), i < j))

    # Clue 20: The person who loves stir fry (food==4) is somewhere to the left of the Prince smoker (cigar==1).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(F[i] == 4, C[j] == 1), i < j))

    # Clue 21: There are two houses between the person who loves eating grilled cheese (food==3) and the person who is super tall (height==5).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(F[i] == 3, H[j] == 5), Or(i == j + 3, i == j - 3)))

    # Clue 22: The person in a ranch-style home (style==0) is the person who smokes Blue Master (cigar==4).
    for i in range(num_houses):
        solver.add(Implies(S[i] == 0, C[i] == 4))
        solver.add(Implies(C[i] == 4, S[i] == 0))

    # Clue 23: The person who smokes many unique blends (cigar==5) is directly left of the person who smokes Blue Master (cigar==4).
    for i in range(num_houses - 1):
        solver.add(Implies(C[i] == 5, C[i+1] == 4))
    # Also, the last house cannot have blends.
    solver.add(C[num_houses - 1] != 5)

    # Clue 24: The person who goes on cultural tours (vacation==0) is the person who is a pizza lover (food==0).
    for i in range(num_houses):
        solver.add(Implies(V[i] == 0, F[i] == 0))
        solver.add(Implies(F[i] == 0, V[i] == 0))

    # Clue 25: The person who is a pizza lover (food==0) is somewhere to the left of the person who likes going on cruises (vacation==1).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(F[i] == 0, V[j] == 1), i < j))

    # Check if the constraints are satisfiable, and print the solution.
    if solver.check() == sat:
        model = solver.model()
        solution_rows = []
        for i in range(num_houses):
            house_number = str(i + 1)
            name_val = names_enum[model.evaluate(N[i]).as_long()]
            style_val = styles_enum[model.evaluate(S[i]).as_long()]
            food_val = foods_enum[model.evaluate(F[i]).as_long()]
            vacation_val = vacations_enum[model.evaluate(V[i]).as_long()]
            height_val = heights_enum[model.evaluate(H[i]).as_long()]
            cigar_val = cigars_enum[model.evaluate(C[i]).as_long()]
            solution_rows.append([house_number, name_val, style_val, food_val, vacation_val, height_val, cigar_val])
        
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": "unsat"}))

if __name__ == "__main__":
    main()