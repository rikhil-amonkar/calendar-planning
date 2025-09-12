from z3 import *
import json

def main():
    # Define the meetings: [name, location, available_start (min from 9:00), available_end, min_duration]
    meetings = [
        ("Ronald", "Russian Hill", 285, 495, 105),
        ("Patricia", "Sunset District", 15, 780, 60),
        ("Laura", "North Beach", 210, 225, 15),
        ("Emily", "The Castro", 435, 570, 60),
        ("Mary", "Golden Gate Park", 360, 450, 60)
    ]
    
    travel_dict = {
        ("Financial District", "Russian Hill"): 10,
        ("Financial District", "Sunset District"): 31,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Golden Gate Park"): 23,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("The Castro", "Financial District"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "The Castro"): 13
    }
    
    n = len(meetings)
    s = Optimize()
    
    held = [Bool(f"held_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    
    order = [[Bool(f"order_{i}_{j}") for j in range(n)] for i in range(n)]
    
    for i in range(n):
        name, loc, avail_start, avail_end, min_dur = meetings[i]
        s.add(Implies(held[i], start[i] >= avail_start))
        s.add(Implies(held[i], end[i] == start[i] + min_dur))
        s.add(Implies(held[i], end[i] <= avail_end))
        travel_time_from_start = travel_dict[("Financial District", loc)]
        s.add(Implies(held[i], start[i] >= travel_time_from_start))
    
    s.add(Implies(held[2], start[2] == 210))
    
    for i in range(n):
        for j in range(i+1, n):
            both_held = And(held[i], held[j])
            s.add(Implies(both_held, Or(order[i][j], order[j][i])))
            s.add(Implies(both_held, Not(And(order[i][j], order[j][i]))))
            
            travel_ij = travel_dict[(meetings[i][1], meetings[j][1])]
            s.add(Implies(And(both_held, order[i][j]), start[j] >= end[i] + travel_ij))
            
            travel_ji = travel_dict[(meetings[j][1], meetings[i][1])]
            s.add(Implies(And(both_held, order[j][i]), start[i] >= end[j] + travel_ji))
    
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for k in range(n):
                if i == k or j == k:
                    continue
                s.add(Implies(And(held[i], held[j], held[k], order[i][j], order[j][k]), order[i][k]))
    
    total_held = Sum([If(held[i], 1, 0) for i in range(n)])
    s.maximize(total_held)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            if is_true(m.evaluate(held[i])):
                start_val = m.evaluate(start[i])
                end_val = m.evaluate(end[i])
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                start_hour = 9 + start_min // 60
                start_minute = start_min % 60
                end_hour = 9 + end_min // 60
                end_minute = end_min % 60
                start_time = f"{start_hour}:{start_minute:02d}"
                end_time = f"{end_hour}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": meetings[i][1],
                    "person": meetings[i][0],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()