from z3 import *
import json

def main():
    # Define meetings and their properties
    n = 4
    names = ["Barbara", "Margaret", "Kevin", "Kimberly"]
    durations = [60, 30, 30, 30]
    windows = [
        (285, 675),  # Barbara: 1:45 PM to 8:15 PM (min start: 285 min from 9:00 AM, max end: 675 min)
        (75, 375),   # Margaret: 10:15 AM to 3:15 PM
        (660, 705),  # Kevin: 8:00 PM to 8:45 PM
        (0, 465)     # Kimberly: 9:00 AM to 4:45 PM (0 min to 465 min from 9:00 AM)
    ]
    travel_start = [21, 31, 19, 17]  # Travel from Bayview to each friend's location
    travel_between = [
        [0, 17, 18, 7],   # From North Beach to others
        [18, 0, 15, 22],   # From Presidio to others
        [19, 15, 0, 17],   # From Haight-Ashbury to others
        [10, 24, 18, 0]    # From Union Square to others
    ]
    
    # Initialize Z3 solver and variables
    opt = Optimize()
    scheduled = [Bool(f's_{i}') for i in range(n)]
    start_t = [Real(f't_{i}') for i in range(n)]
    imm_before = [[Bool(f'imm_{i}_{j}') for j in range(n)] for i in range(n)]
    
    # Time window constraints
    for i in range(n):
        opt.add(Implies(scheduled[i], And(
            start_t[i] >= windows[i][0],
            start_t[i] + durations[i] <= windows[i][1]
        )))
    
    # Constraints for immediate predecessors
    for i in range(n):
        for j in range(n):
            opt.add(Implies(imm_before[i][j], And(scheduled[i], scheduled[j])))
    
    # Predecessor and sequence constraints
    no_pred_list = []
    for j in range(n):
        no_pred = And(scheduled[j], *[Not(imm_before[i][j]) for i in range(n)])
        no_pred_list.append(no_pred)
        has_pred = Or([imm_before[i][j] for i in range(n)])
        opt.add(Implies(scheduled[j], Or(Not(has_pred), has_pred)))
    
    k = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    total_edges = Sum([If(imm_before[i][j], 1, 0) for i in range(n) for j in range(n)])
    opt.add(total_edges == k - 1)
    opt.add(Sum([If(no_pred_list[j], 1, 0) for j in range(n)]) == 1)
    
    for i in range(n):
        out_edges = Sum([If(imm_before[i][j], 1, 0) for j in range(n)])
        opt.add(out_edges <= 1)
    
    # Travel time constraints
    for j in range(n):
        opt.add(Implies(no_pred_list[j], start_t[j] >= travel_start[j]))
        for i in range(n):
            opt.add(Implies(imm_before[i][j], 
                            start_t[j] >= start_t[i] + durations[i] + travel_between[i][j]))
    
    # Maximize the number of meetings
    opt.maximize(k)
    
    # Solve and extract solution
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n):
            if m.evaluate(scheduled[i]):
                start_val = m.evaluate(start_t[i])
                if is_rational_value(start_val):
                    num = start_val.numerator_as_long()
                    den = start_val.denominator_as_long()
                    minutes = num // den
                else:
                    minutes = start_val.as_long()
                hour = 9 + minutes // 60
                minute = minutes % 60
                start_time = f"{hour:02d}:{minute:02d}"
                end_minutes = minutes + durations[i]
                end_hour = 9 + end_minutes // 60
                end_minute = end_minutes % 60
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()