import itertools
from z3 import *
import json

def min_to_time(total_minutes):
    total_minutes_abs = 9 * 60 + total_minutes
    hours = total_minutes_abs // 60
    minutes = total_minutes_abs % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    friends_data = [
        {"name": "David", "loc": "FW", "min_dur": 15, "avail_start": 105, "avail_end": 390},
        {"name": "Timothy", "loc": "PH", "min_dur": 75, "avail_start": 0, "avail_end": 390},
        {"name": "Robert", "loc": "MD", "min_dur": 90, "avail_start": 195, "avail_end": 645}
    ]
    
    travel_times = {
        "FD": {"FW": 10, "PH": 13, "MD": 17},
        "FW": {"FD": 11, "PH": 12, "MD": 22},
        "PH": {"FD": 13, "FW": 13, "MD": 15},
        "MD": {"FD": 17, "FW": 22, "PH": 16}
    }
    
    solver = Solver()
    schedule = None
    found = False
    
    # Try all permutations for three meetings
    perms = list(itertools.permutations([0, 1, 2]))
    for perm in perms:
        f0 = friends_data[perm[0]]
        f1 = friends_data[perm[1]]
        f2 = friends_data[perm[2]]
        
        s0 = Int(f's0_{perm}')
        s1 = Int(f's1_{perm}')
        s2 = Int(f's2_{perm}')
        
        constraints = [
            s0 >= travel_times["FD"][f0["loc"]],
            s1 >= s0 + f0["min_dur"] + travel_times[f0["loc"]][f1["loc"]],
            s2 >= s1 + f1["min_dur"] + travel_times[f1["loc"]][f2["loc"]],
            s0 >= f0["avail_start"],
            s0 + f0["min_dur"] <= f0["avail_end"],
            s1 >= f1["avail_start"],
            s1 + f1["min_dur"] <= f1["avail_end"],
            s2 >= f2["avail_start"],
            s2 + f2["min_dur"] <= f2["avail_end"],
            s0 >= 0,
            s1 >= 0,
            s2 >= 0
        ]
        
        solver.push()
        solver.add(constraints)
        if solver.check() == sat:
            m = solver.model()
            start0 = m.eval(s0).as_long()
            start1 = m.eval(s1).as_long()
            start2 = m.eval(s2).as_long()
            
            itinerary = [
                {"action": "meet", "person": f0["name"], "start_time": min_to_time(start0), "end_time": min_to_time(start0 + f0["min_dur"])},
                {"action": "meet", "person": f1["name"], "start_time": min_to_time(start1), "end_time": min_to_time(start1 + f1["min_dur"])},
                {"action": "meet", "person": f2["name"], "start_time": min_to_time(start2), "end_time": min_to_time(start2 + f2["min_dur"])}
            ]
            schedule = itinerary
            found = True
            solver.pop()
            break
        else:
            solver.pop()
    
    if not found:
        pairs = list(itertools.combinations([0, 1, 2], 2))
        for pair in pairs:
            orders = list(itertools.permutations(pair, 2))
            for ord in orders:
                f0 = friends_data[ord[0]]
                f1 = friends_data[ord[1]]
                
                s0 = Int(f's0_{ord}')
                s1 = Int(f's1_{ord}')
                
                constraints = [
                    s0 >= travel_times["FD"][f0["loc"]],
                    s1 >= s0 + f0["min_dur"] + travel_times[f0["loc"]][f1["loc"]],
                    s0 >= f0["avail_start"],
                    s0 + f0["min_dur"] <= f0["avail_end"],
                    s1 >= f1["avail_start"],
                    s1 + f1["min_dur"] <= f1["avail_end"],
                    s0 >= 0,
                    s1 >= 0
                ]
                
                solver.push()
                solver.add(constraints)
                if solver.check() == sat:
                    m = solver.model()
                    start0 = m.eval(s0).as_long()
                    start1 = m.eval(s1).as_long()
                    
                    itinerary = [
                        {"action": "meet", "person": f0["name"], "start_time": min_to_time(start0), "end_time": min_to_time(start0 + f0["min_dur"])},
                        {"action": "meet", "person": f1["name"], "start_time": min_to_time(start1), "end_time": min_to_time(start1 + f1["min_dur"])}
                    ]
                    schedule = itinerary
                    found = True
                    solver.pop()
                    break
                else:
                    solver.pop()
            if found:
                break
    
    if not found:
        for i in range(3):
            f = friends_data[i]
            s_var = Int(f's_single_{i}')
            constraints = [
                s_var >= travel_times["FD"][f["loc"]],
                s_var >= f["avail_start"],
                s_var + f["min_dur"] <= f["avail_end"],
                s_var >= 0
            ]
            solver.push()
            solver.add(constraints)
            if solver.check() == sat:
                m = solver.model()
                start_val = m.eval(s_var).as_long()
                schedule = [
                    {"action": "meet", "person": f["name"], "start_time": min_to_time(start_val), "end_time": min_to_time(start_val + f["min_dur"])}
                ]
                found = True
                solver.pop()
                break
            else:
                solver.pop()
    
    if schedule is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": schedule}
    print(json.dumps(result))

if __name__ == "__main__":
    main()