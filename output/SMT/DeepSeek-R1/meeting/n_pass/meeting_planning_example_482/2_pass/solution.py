from z3 import *
import json

def main():
    # Travel times dictionary: keys are (from_location, to_location)
    travel_times = {
        (0,1): 11, (0,2): 18, (0,4): 17, (0,5): 23,
        (1,0): 12, (1,2): 15, (1,4): 15, (1,5): 22,
        (2,0): 19, (2,1): 13, (2,4): 23, (2,5): 25,
        (4,0): 17, (4,1): 16, (4,2): 23, (4,5): 7,
        (5,0): 22, (5,1): 22, (5,2): 26, (5,4): 7
    }
    
    # Meeting details: index, name, location, duration (min), min_start (minutes), max_end (minutes)
    meetings = [
        {'idx': 0, 'name': 'Stephanie', 'loc': 1, 'dur': 90, 'min_start': 495, 'max_end': 825},  # 8:15AM to 1:45PM
        {'idx': 1, 'name': 'Brian', 'loc': 4, 'dur': 120, 'min_start': 735, 'max_end': 960},      # 12:15PM to 4:00PM
        {'idx': 2, 'name': 'Jason', 'loc': 5, 'dur': 60, 'min_start': 510, 'max_end': 1065},     # 8:30AM to 5:45PM
        {'idx': 3, 'name': 'Sandra', 'loc': 2, 'dur': 15, 'min_start': 780, 'max_end': 1170}     # 1:00PM to 7:30PM
    ]
    
    # Extract locations and durations for each meeting index
    locs = [m['loc'] for m in meetings]
    durations = [m['dur'] for m in meetings]
    names = [m['name'] for m in meetings]
    
    s = Solver()
    
    # Order variables: o0 = first meeting, o1 = second, etc.
    o0, o1, o2, o3 = Ints('o0 o1 o2 o3')
    order = [o0, o1, o2, o3]
    
    # Start time variables for each meeting (by their index)
    s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
    start_times = [s0, s1, s2, s3]
    
    # End times are computed
    e0 = s0 + durations[0]
    e1 = s1 + durations[1]
    e2 = s2 + durations[2]
    e3 = s3 + durations[3]
    end_times = [e0, e1, e2, e3]
    
    # Constraints: order must be a permutation of [0,1,2,3]
    s.add(Distinct(o0, o1, o2, o3))
    for o in order:
        s.add(o >= 0, o < 4)
    
    # Time window constraints for each meeting
    for i, m in enumerate(meetings):
        s.add(start_times[i] >= m['min_start'])
        s.add(end_times[i] <= m['max_end'])
    
    # Constraints for the first meeting: start time = 540 (9:00AM) + travel time from Haight-Ashbury (0) to the meeting's location
    for i in range(4):
        s.add(Implies(o0 == i, start_times[i] == 540 + travel_times[(0, locs[i])]))
    
    # Constraints for the second meeting: start time >= end time of first meeting + travel time between locations
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            s.add(Implies(And(o0 == i, o1 == j), 
                         start_times[j] >= start_times[i] + durations[i] + travel_times[(locs[i], locs[j])]))
    
    # Constraints for the third meeting
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            s.add(Implies(And(o1 == i, o2 == j), 
                         start_times[j] >= start_times[i] + durations[i] + travel_times[(locs[i], locs[j])]))
    
    # Constraints for the fourth meeting
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            s.add(Implies(And(o2 == i, o3 == j), 
                         start_times[j] >= start_times[i] + durations[i] + travel_times[(locs[i], locs[j])]))
    
    if s.check() == sat:
        model = s.model()
        # Get the order of meetings
        order_vals = [model[o].as_long() for o in order]
        # Get start times for each meeting
        start_vals = [model[st].as_long() for st in start_times]
        
        itinerary = []
        for idx in order_vals:
            meeting = meetings[idx]
            start_minutes = start_vals[idx]
            end_minutes = start_minutes + meeting['dur']
            # Convert to HH:MM format
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}"
            })
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()