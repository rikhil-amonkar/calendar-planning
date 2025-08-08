from z3 import *
import json

def main():
    travel_times = {
        (0,1): 11, (0,2): 18, (0,4): 17, (0,5): 23,
        (1,0): 12, (1,2): 15, (1,4): 15, (1,5): 22,
        (2,0): 19, (2,1): 13, (2,4): 23, (2,5): 25,
        (4,0): 17, (4,1): 16, (4,2): 23, (4,5): 7,
        (5,0): 22, (5,1): 22, (5,2): 26, (5,4): 7
    }
    
    meetings = [
        {'idx': 0, 'name': 'Stephanie', 'loc': 1, 'dur': 90, 'min_start': 495, 'max_end': 825},
        {'idx': 1, 'name': 'Brian', 'loc': 4, 'dur': 120, 'min_start': 735, 'max_end': 960},
        {'idx': 2, 'name': 'Jason', 'loc': 5, 'dur': 60, 'min_start': 510, 'max_end': 1065},
        {'idx': 3, 'name': 'Sandra', 'loc': 2, 'dur': 15, 'min_start': 780, 'max_end': 1170}
    ]
    
    locs = [m['loc'] for m in meetings]
    durations = [m['dur'] for m in meetings]
    
    s = Solver()
    
    # Order variables
    o0, o1, o2, o3 = Ints('o0 o1 o2 o3')
    order = [o0, o1, o2, o3]
    
    # Start time variables
    s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
    start_times = [s0, s1, s2, s3]
    e0 = s0 + durations[0]
    e1 = s1 + durations[1]
    e2 = s2 + durations[2]
    e3 = s3 + durations[3]
    end_times = [e0, e1, e2, e3]
    
    # Order must be permutation of meeting indices
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 0, o < 4)
    
    # Time window constraints
    for i, m in enumerate(meetings):
        s.add(start_times[i] >= m['min_start'])
        s.add(end_times[i] <= m['max_end'])
    
    # First meeting starts at 9:00 AM + travel time from Haight-Ashbury
    for i in range(4):
        s.add(Implies(o0 == i, start_times[i] >= 540 + travel_times[(0, locs[i])]))
    
    # Subsequent meetings start after previous meeting + travel time
    for i in range(4):
        for j in range(4):
            if i != j:
                # Order 0 -> 1
                s.add(Implies(And(o0 == i, o1 == j),
                         start_times[j] >= end_times[i] + travel_times[(locs[i], locs[j])]))
                # Order 1 -> 2
                s.add(Implies(And(o1 == i, o2 == j),
                         start_times[j] >= end_times[i] + travel_times[(locs[i], locs[j])]))
                # Order 2 -> 3
                s.add(Implies(And(o2 == i, o3 == j),
                         start_times[j] >= end_times[i] + travel_times[(locs[i], locs[j])]))
    
    if s.check() == sat:
        model = s.model()
        order_vals = [model[o].as_long() for o in order]
        start_vals = [model[st].as_long() for st in start_times]
        
        itinerary = []
        for idx in order_vals:
            meeting = meetings[idx]
            start_minutes = start_vals[idx]
            end_minutes = start_minutes + meeting['dur']
            start_time = f"{start_minutes//60:02d}:{start_minutes%60:02d}"
            end_time = f"{end_minutes//60:02d}:{end_minutes%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": start_time,
                "end_time": end_time
            })
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()