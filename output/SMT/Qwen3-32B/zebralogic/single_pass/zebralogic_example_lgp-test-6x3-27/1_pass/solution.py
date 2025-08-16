from z3 import *
import json

solver = Solver()

# Create variables for each house's name, occupation, car
name_vars = [Int(f"name_{i}") for i in range(1, 7)]
occupation_vars = [Int(f"occupation_{i}") for i in range(1, 7)]
car_vars = [Int(f"car_{i}") for i in range(1, 7)]

# Add constraints that each attribute is a permutation (0-5, distinct)
for attr in [name_vars, occupation_vars, car_vars]:
    for v in attr:
        solver.add(And(0 <= v, v <= 5))
    solver.add(Distinct(attr))

# Add direct constraints from clues
solver.add(car_vars[5] == 1)  # clue 1
solver.add(car_vars[2] != 0)  # clue 2
solver.add(occupation_vars[5] != 5)  # clue 4
solver.add(name_vars[6] != 5)  # clue 9

# Create auxiliary variables for positions
H_civic = Int('H_civic')
P_peter = Int('P_peter')
A_arnold = Int('A_arnold')
E_eric = Int('E_eric')
C_carol = Int('C_carol')
B_bob = Int('B_bob')
L_lawyer = Int('L_lawyer')
T_tesla = Int('T_tesla')
T_teacher = Int('T_teacher')
N_nurse = Int('N_nurse')

for var in [H_civic, P_peter, A_arnold, E_eric, C_carol, B_bob, L_lawyer, T_tesla, T_teacher, N_nurse]:
    solver.add(And(1 <= var, var <= 6))

# Constraints for auxiliary variables to match their definitions
for h in range(1, 7):
    # Honda Civic (car 2) is in H_civic
    solver.add((car_vars[h] == 2) == (H_civic == h))
    # Peter (name 3) is in P_peter
    solver.add((name_vars[h] == 3) == (P_peter == h))
    # Arnold (name 1) is in A_arnold
    solver.add((name_vars[h] == 1) == (A_arnold == h))
    # Eric (name 2) is in E_eric
    solver.add((name_vars[h] == 2) == (E_eric == h))
    # Carol (name 5) is in C_carol
    solver.add((name_vars[h] == 5) == (C_carol == h))
    # Bob (name 4) is in B_bob
    solver.add((name_vars[h] == 4) == (B_bob == h))
    # Lawyer (occupation 5) is in L_lawyer
    solver.add((occupation_vars[h] == 5) == (L_lawyer == h))
    # Tesla (car 5) is in T_tesla
    solver.add((car_vars[h] == 5) == (T_tesla == h))
    # Teacher (occupation 3) is in T_teacher
    solver.add((occupation_vars[h] == 3) == (T_teacher == h))
    # Nurse (occupation 4) is in N_nurse
    solver.add((occupation_vars[h] == 4) == (N_nurse == h))

# Add constraints based on the clues
solver.add(Abs(H_civic - P_peter) == 1)  # clue 3
solver.add(A_arnold == N_nurse + 1)  # clue 5
solver.add(car_vars[N_nurse] == 3)  # clue 5 and 11
solver.add(C_carol > E_eric)  # clue 6
solver.add(occupation_vars[E_eric] == 2)  # clue 7
solver.add(T_teacher < N_nurse)  # clue 8
solver.add(occupation_vars[B_bob] == 0)  # clue 10
solver.add(occupation_vars[A_arnold] == 1)  # clue 14
solver.add(Abs(P_peter - L_lawyer) == 2)  # clue 12
solver.add(Abs(T_tesla - B_bob) == 2)  # clue 13
solver.add(L_lawyer != 5)  # clue 4

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Now extract the solution for each house
    solution = []
    for house_num in range(1, 7):
        idx = house_num - 1
        name_idx = model[name_vars[idx]].as_long()
        occ_idx = model[occupation_vars[idx]].as_long()
        car_idx = model[car_vars[idx]].as_long()
        name = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"][name_idx]
        occ = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"][occ_idx]
        car = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"][car_idx]
        solution.append([str(house_num), name, occ, car])
    # Output in the required JSON format
    json_output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")