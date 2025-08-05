from z3 import *
import itertools
import json

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    meetings = [
        {
            "name": "Melissa",
            "location": "North Beach",
            "available_start": 8*60 + 15,  # 8:15 AM
            "available_end": 13*60 + 30,    # 1:30 PM
            "min_dur": 105
        },
        {
            "name": "Anthony",
            "location": "Chinatown",
            "available_start": 13*60 + 15,  # 1:15 PM
            "available_end": 14*60 + 30,    # 2:30 PM
            "min_dur": 60
        },
        {
            "name": "Rebecca",
            "location": "Russian Hill",
            "available_start": 19*60 + 30,  # 7:30 PM
            "available_end": 21*60 + 15,    # 9:15 PM
            "min_dur": 105
        }
    ]
    
    travel_times = {
        ("Sunset", "North Beach"): 29,
        ("Sunset", "Chinatown"): 30,
        ("Sunset", "Russian Hill"): 24,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Russian Hill"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9
    }
    
    perms = list(itertools.permutations([0, 1, 2]))
    solution_found = False
    itinerary = []
    
    for p in perms:
        m0 = meetings[p[0]]
        m1 = meetings[p[1]]
        m2 = meetings[p[2]]
        
        try:
            t0 = travel_times[("Sunset", m0["location"])]
            t1 = travel_times[(m0["location"], m1["location"])]
            t2 = travel_times[(m1["location"], m2["location"])]
        except KeyError:
            continue
            
        s0 = Int(f's0_{p}')
        s1 = Int(f's1_{p}')
        s2 = Int(f's2_{p}')
        
        d0 = m0["min_dur"]
        d1 = m1["min_dur"]
        d2 = m2["min_dur"]
        
        solver = Solver()
        
        solver.add(s0 >= 540 + t0)
        solver.add(s0 >= m0["available_start"])
        solver.add(s0 + d0 <= m0["available_end"])
        
        solver.add(s1 >= s0 + d0 + t1)
        solver.add(s1 >= m1["available_start"])
        solver.add(s1 + d1 <= m1["available_end"])
        
        solver.add(s2 >= s1 + d1 + t2)
        solver.add(s2 >= m2["available_start"])
        solver.add(s2 + d2 <= m2["available_end"])
        
        if solver.check() == sat:
            model = solver.model()
            start0 = model[s0].as_long()
            start1 = model[s1].as_long()
            start2 = model[s2].as_long()
            
            itinerary = [
                {"action": "meet", "person": m0["name"], "start_time": min_to_time(start0), "end_time": min_to_time(start0 + d0)},
                {"action": "meet", "person": m1["name"], "start_time": min_to_time(start1), "end_time": min_to_time(start1 + d1)},
                {"action": "meet", "person": m2["name"], "start_time": min_to_time(start2), "end_time": min_to_time(start2 + d2)}
            ]
            solution_found = True
            break
            
    if not solution_found:
        result = {"itinerary": []}
    else:
        result = {"itinerary": itinerary}
    
    print("SOLUTION:")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()