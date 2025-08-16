# Solve the logic puzzle with Z3 and output the JSON solution.
from z3 import *
import json

def solve():
    n = 5
    H = range(n)  # houses 0..4 representing 1..5

    # Enumerations
    N_BOB, N_ERIC, N_ARNOLD, N_ALICE, N_PETER = range(5)
    C_BLUE, C_GREEN, C_WHITE, C_YELLOW, C_RED = range(5)
    P_HUAWEI, P_SAMSUNG, P_ONEPLUS, P_IPHONE, P_PIXEL = range(5)
    O_ARTIST, O_TEACHER, O_DOCTOR, O_ENGINEER, O_LAWYER = range(5)

    # Variables: attribute index assigned to each house
    name = [Int(f"name_{i}") for i in H]
    color = [Int(f"color_{i}") for i in H]
    phone = [Int(f"phone_{i}") for i in H]
    occ = [Int(f"occ_{i}") for i in H]

    s = Solver()

    # Domains
    for i in H:
        s.add(And(name[i] >= 0, name[i] < 5))
        s.add(And(color[i] >= 0, color[i] < 5))
        s.add(And(phone[i] >= 0, phone[i] < 5))
        s.add(And(occ[i] >= 0, occ[i] < 5))

    # Uniqueness across houses
    s.add(Distinct(name))
    s.add(Distinct(color))
    s.add(Distinct(phone))
    s.add(Distinct(occ))

    # Helper: Or over empty list is False; avoid empties
    def any_right_of(idx_list, i):
        return Or([And(j > i, idx_list[j]) for j in H]) if any(True for _ in H) else False

    def any_left_of(idx_list, i):
        return Or([And(j < i, idx_list[j]) for j in H]) if any(True for _ in H) else False

    # Clues

    # 1. The person who is an engineer is somewhere to the right of the person who is a lawyer.
    for i in H:
        s.add(Implies(occ[i] == O_ENGINEER, Or([And(j < i, occ[j] == O_LAWYER) for j in H])))

    # 2. Bob is in the second house. (index 1)
    s.add(name[1] == N_BOB)

    # 3. Samsung Galaxy S21 user is the doctor.
    for i in H:
        s.add((phone[i] == P_SAMSUNG) == (occ[i] == O_DOCTOR))

    # 4. The doctor loves blue.
    for i in H:
        s.add((occ[i] == O_DOCTOR) == (color[i] == C_BLUE))

    # 5. Green is not in the fifth house. (index 4)
    s.add(color[4] != C_GREEN)

    # 6. The lawyer uses a OnePlus 9.
    for i in H:
        s.add((occ[i] == O_LAWYER) == (phone[i] == P_ONEPLUS))

    # 7. Blue is directly left of red.
    s.add(Or([And(color[i] == C_BLUE, color[i+1] == C_RED) for i in range(n-1)]))

    # 8. The lawyer is somewhere to the right of the Samsung user.
    for i in H:
        s.add(Implies(occ[i] == O_LAWYER, Or([And(j < i, phone[j] == P_SAMSUNG) for j in H])))

    # 9. There is one house between the Google Pixel 6 and the Huawei P50.
    for i in H:
        left_ok = And(i - 2 >= 0, phone[i-2] == P_HUAWEI)
        right_ok = And(i + 2 < n, phone[i+2] == P_HUAWEI)
        s.add(Implies(phone[i] == P_PIXEL, Or(left_ok, right_ok)))
    for i in H:
        left_ok = And(i - 2 >= 0, phone[i-2] == P_PIXEL)
        right_ok = And(i + 2 < n, phone[i+2] == P_PIXEL)
        s.add(Implies(phone[i] == P_HUAWEI, Or(left_ok, right_ok)))

    # 10. Arnold is the engineer.
    for i in H:
        s.add((name[i] == N_ARNOLD) == (occ[i] == O_ENGINEER))

    # 11. Alice loves yellow.
    for i in H:
        s.add((name[i] == N_ALICE) == (color[i] == C_YELLOW))

    # 12. Google Pixel 6 user is Eric.
    for i in H:
        s.add((phone[i] == P_PIXEL) == (name[i] == N_ERIC))

    # 13. Google Pixel 6 user is the teacher.
    for i in H:
        s.add((phone[i] == P_PIXEL) == (occ[i] == O_TEACHER))

    # 14. Red is somewhere to the right of the teacher.
    for i in H:
        s.add(Implies(occ[i] == O_TEACHER, Or([color[j] == C_RED for j in range(i+1, n)])))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    colors = ["blue", "green", "white", "yellow", "red"]
    phones = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    occs = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    rows = []
    for i in H:
        rows.append([
            str(i + 1),
            names[m[name[i]].as_long()],
            colors[m[color[i]].as_long()],
            phones[m[phone[i]].as_long()],
            occs[m[occ[i]].as_long()],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    res = solve()
    print(json.dumps(res, ensure_ascii=False, indent=2))