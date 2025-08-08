from z3 import *
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    T_start = Int('T_start')
    D_start = Int('D_start')
    R_start = Int('R_start')
    
    s = Solver()
    
    # Availability constraints
    s.add(T_start >= 540)       # 9:00 AM
    s.add(T_start + 75 <= 930)  # 3:30 PM
    s.add(D_start >= 645)       # 10:45 AM
    s.add(D_start + 15 <= 930)  # 3:30 PM
    s.add(R_start >= 735)       # 12:15 PM
    s.add(R_start + 90 <= 1185) # 7:45 PM
    
    # Travel times for each permutation
    perm_travels = [
        (13, 13, 22),   # T, D, R
        (13, 15, 22),   # T, R, D
        (10, 12, 15),   # D, T, R
        (10, 22, 16),   # D, R, T
        (17, 16, 13),   # R, T, D
        (17, 22, 12)    # R, D, T
    ]
    
    # Constraints for each permutation
    constraints = []
    
    # Permutation 0: T, D, R
    c0 = And(
        540 + perm_travels[0][0] <= T_start,
        T_start + 75 + perm_travels[0][1] <= D_start,
        D_start + 15 + perm_travels[0][2] <= R_start
    )
    constraints.append(c0)
    
    # Permutation 1: T, R, D
    c1 = And(
        540 + perm_travels[1][0] <= T_start,
        T_start + 75 + perm_travels[1][1] <= R_start,
        R_start + 90 + perm_travels[1][2] <= D_start
    )
    constraints.append(c1)
    
    # Permutation 2: D, T, R
    c2 = And(
        540 + perm_travels[2][0] <= D_start,
        D_start + 15 + perm_travels[2][1] <= T_start,
        T_start + 75 + perm_travels[2][2] <= R_start
    )
    constraints.append(c2)
    
    # Permutation 3: D, R, T
    c3 = And(
        540 + perm_travels[3][0] <= D_start,
        D_start + 15 + perm_travels[3][1] <= R_start,
        R_start + 90 + perm_travels[3][2] <= T_start
    )
    constraints.append(c3)
    
    # Permutation 4: R, T, D
    c4 = And(
        540 + perm_travels[4][0] <= R_start,
        R_start + 90 + perm_travels[4][1] <= T_start,
        T_start + 75 + perm_travels[4][2] <= D_start
    )
    constraints.append(c4)
    
    # Permutation 5: R, D, T
    c5 = And(
        540 + perm_travels[5][0] <= R_start,
        R_start + 90 + perm_travels[5][1] <= D_start,
        D_start + 15 + perm_travels[5][2] <= T_start
    )
    constraints.append(c5)
    
    s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        t_val = m.eval(T_start).as_long()
        d_val = m.eval(D_start).as_long()
        r_val = m.eval(R_start).as_long()
        
        meetings = [
            (t_val, "Timothy", 75),
            (d_val, "David", 15),
            (r_val, "Robert", 90)
        ]
        meetings_sorted = sorted(meetings, key=lambda x: x[0])
        
        itinerary = []
        for start, person, dur in meetings_sorted:
            end = start + dur
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": format_time(start),
                "end_time": format_time(end)
            })
        
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION: {\"itinerary\": []}")

if __name__ == "__main__":
    main()