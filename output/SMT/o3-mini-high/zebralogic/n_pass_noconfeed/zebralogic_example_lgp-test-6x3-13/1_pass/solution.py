from z3 import *
import json

def main():
    solver = Solver()
    
    # There are 6 houses indexed 0 to 5 (house 1 is index 0, house 6 is index 5)
    n_houses = 6

    # Create integer variables for each house attribute:
    # For names: Bob=0, Arnold=1, Carol=2, Alice=3, Peter=4, Eric=5
    # For book genres: romance=0, historical fiction=1, biography=2, mystery=3, fantasy=4, science fiction=5
    # For occupations: artist=0, doctor=1, nurse=2, engineer=3, teacher=4, lawyer=5
    names = [Int(f"name_{i}") for i in range(n_houses)]
    books = [Int(f"book_{i}") for i in range(n_houses)]
    occs  = [Int(f"occ_{i}") for i in range(n_houses)]
    
    # Domain constraints for each variable: values between 0 and 5
    for i in range(n_houses):
        solver.add(And(names[i] >= 0, names[i] < 6))
        solver.add(And(books[i] >= 0, books[i] < 6))
        solver.add(And(occs[i]  >= 0, occs[i]  < 6))
    
    # All attributes are distinct (each is a permutation)
    solver.add(Distinct(names))
    solver.add(Distinct(books))
    solver.add(Distinct(occs))
    
    # Clue 1: Alice is the person who loves fantasy books.
    # (Alice = 3, fantasy = 4)
    for i in range(n_houses):
        solver.add(Implies(names[i] == 3, books[i] == 4))
        solver.add(Implies(books[i] == 4, names[i] == 3))
    
    # Clue 2: The person who loves mystery books and Bob are next to each other.
    # (Bob = 0, mystery = 3)
    for i in range(n_houses):
        for j in range(n_houses):
            solver.add(Implies(And(names[i] == 0, books[j] == 3), Or(j == i + 1, j == i - 1)))
    
    # Clue 3: Carol is the person who loves mystery books.
    # (Carol = 2, mystery = 3)
    for i in range(n_houses):
        solver.add(Implies(names[i] == 2, books[i] == 3))
        solver.add(Implies(books[i] == 3, names[i] == 2))
    
    # Clue 4: The person who is a lawyer is the person who loves fantasy books.
    # (lawyer = 5, fantasy = 4)
    for i in range(n_houses):
        solver.add(Implies(occs[i] == 5, books[i] == 4))
        solver.add(Implies(books[i] == 4, occs[i] == 5))
    
    # Clue 5: Bob is not in the fifth house. (House 5 is index 4)
    solver.add(names[4] != 0)
    
    # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
    # (Arnold = 1, engineer = 3)
    for i in range(n_houses):
        for j in range(n_houses):
            solver.add(Implies(And(names[i] == 1, occs[j] == 3), i < j))
    
    # Clue 7: The person who is a nurse is directly left of Alice.
    # (nurse = 2, Alice = 3) => There exists an index i (0 <= i < 5) with nurse and house i+1 is Alice.
    nurse_left_alice = [And(occs[i] == 2, names[i+1] == 3) for i in range(n_houses - 1)]
    solver.add(Or(nurse_left_alice))
    
    # Clue 8: The person who loves biography books is the person who is a teacher.
    # (biography = 2, teacher = 4)
    for i in range(n_houses):
        solver.add(Implies(books[i] == 2, occs[i] == 4))
        solver.add(Implies(occs[i] == 4, books[i] == 2))
    
    # Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    # (historical fiction = 1, teacher = 4)
    for i in range(n_houses):
        for j in range(n_houses):
            solver.add(Implies(And(books[i] == 1, occs[j] == 4), i < j))
    
    # Clue 10: The person who is a doctor is in the first house.
    # (doctor = 1) -> First house is index 0.
    solver.add(occs[0] == 1)
    
    # Clue 11: The person who loves science fiction books is the person who is an artist.
    # (science fiction = 5, artist = 0)
    for i in range(n_houses):
        solver.add(Implies(books[i] == 5, occs[i] == 0))
        solver.add(Implies(occs[i] == 0, books[i] == 5))
    
    # Clue 12: Eric is in the third house.
    # (Eric = 5) -> Third house is index 2.
    solver.add(names[2] == 5)
    
    # Clue 13: The person who loves mystery books is not in the fifth house.
    # (mystery = 3) -> House 5 is index 4.
    solver.add(books[4] != 3)
    
    # Check if the constraints are satisfiable and build the solution output
    if solver.check() == sat:
        m = solver.model()
        # Mapping back from integers to actual attribute names
        names_map = {0: "Bob", 1: "Arnold", 2: "Carol", 3: "Alice", 4: "Peter", 5: "Eric"}
        books_map = {
            0: "romance",
            1: "historical fiction",
            2: "biography",
            3: "mystery",
            4: "fantasy",
            5: "science fiction"
        }
        occs_map = {0: "artist", 1: "doctor", 2: "nurse", 3: "engineer", 4: "teacher", 5: "lawyer"}
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": []
            }
        }
        # Houses are ordered 1 to 6 corresponding to indices 0 to 5
        for i in range(n_houses):
            house_num = str(i + 1)
            name_val = names_map[m.evaluate(names[i]).as_long()]
            book_val = books_map[m.evaluate(books[i]).as_long()]
            occ_val  = occs_map[m.evaluate(occs[i]).as_long()]
            solution["solution"]["rows"].append([house_num, name_val, book_val, occ_val])
        
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()