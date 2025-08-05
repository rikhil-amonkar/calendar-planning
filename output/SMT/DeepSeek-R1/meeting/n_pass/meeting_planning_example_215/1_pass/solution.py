from z3 import *
import json

def main():
    # Meeting indices: 0: Jason, 1: Jessica, 2: Sandra
    names = ["Jason", "Jessica", "Sandra"]
    # Locations: BV=0, E=1, RD=2, FW=3
    loc_index = [3, 1, 2]  # Jason at FW (3), Jessica at E (1), Sandra at RD (2)
    # Availability windows in minutes from 9:00
    window_start_min = [420, 465, 570]  # Jason:16:00, Jessica:16:45, Sandra:18:30
    window_end_min = [465, 600, 765]    # Jason:16:45, Jessica:19:00, Sandra:21:45
    duration_minutes = [30, 30, 120]    # Meeting durations

    # Travel time matrix: [from][to] (0: BV, 1: E, 2: RD, 3: FW)
    travel = [
        [0, 19, 25, 25],  # From BV
        [21, 0, 21, 6],    # From E
        [26, 19, 0, 18],   # From RD
        [26, 8, 18, 0]     # From FW
    ]

    # Create Z3 variables
    meet = [Bool(f"meet_{i}") for i in range(3)]
    start = [Int(f"start_{i}") for i in range(3)]

    s = Solver()

    # Constraints for each meeting if it is scheduled
    for i in range(3):
        loc_i = loc_index[i]
        travel_BV = travel[0][loc_i]  # Travel time from Bayview to meeting location
        s.add(Implies(meet[i], 
                     And(start[i] >= window_start_min[i],
                         start[i] + duration_minutes[i] <= window_end_min[i],
                         start[i] >= travel_BV)))
    
    # Constraints for pairs of meetings
    for i in range(3):
        for j in range(i+1, 3):
            loc_i = loc_index[i]
            loc_j = loc_index[j]
            travel_ij = travel[loc_i][loc_j]  # From i to j
            travel_ji = travel[loc_j][loc_i]  # From j to i
            s.add(Implies(And(meet[i], meet[j]),
                          Or(start[i] + duration_minutes[i] + travel_ij <= start[j],
                             start[j] + duration_minutes[j] + travel_ji <= start[i])))
    
    # Maximize the number of meetings
    opt = Optimize()
    opt.add(s.assertions())
    num_meetings = If(meet[0], 1, 0) + If(meet[1], 1, 0) + If(meet[2], 1, 0)
    opt.maximize(num_meetings)
    
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(3):
            if is_true(m.eval(meet[i])):
                start_val = m.eval(start[i]).as_long()
                end_val = start_val + duration_minutes[i]
                # Convert to total minutes from midnight for formatting
                total_start_min = 9*60 + start_val
                total_end_min = 9*60 + end_val
                h_start = total_start_min // 60
                m_start = total_start_min % 60
                h_end = total_end_min // 60
                m_end = total_end_min % 60
                start_time = f"{h_start:02d}:{m_start:02d}"
                end_time = f"{h_end:02d}:{m_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()