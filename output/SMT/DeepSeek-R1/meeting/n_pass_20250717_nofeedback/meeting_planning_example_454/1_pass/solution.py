from z3 import *

def main():
    # Locations: Presidio, Golden Gate Park, Bayview, Chinatown, North Beach, Mission District
    locations = ["Presidio", "Golden Gate Park", "Bayview", "Chinatown", "North Beach", "Mission District"]
    n_locations = len(locations)
    
    # Travel time matrix: travel[i][j] = time from location i to j
    travel = [
        [0, 12, 31, 21, 18, 26],
        [11, 0, 23, 23, 24, 17],
        [31, 22, 0, 18, 21, 13],
        [19, 23, 22, 0, 3, 18],
        [17, 22, 22, 6, 0, 18],
        [25, 17, 15, 16, 17, 0]
    ]
    
    # Event indices: 
    # 0: start event (Presidio at 9:00)
    # 1: Jessica (Golden Gate Park)
    # 2: Ashley (Bayview)
    # 3: Ronald (Chinatown)
    # 4: William (North Beach)
    # 5: Daniel (Mission District)
    
    # Windows in minutes (start, end) for events 0 to 5
    windows = {
        0: (540, 540),   # 9:00
        1: (825, 900),   # Jessica: 1:45 PM to 3:00 PM
        2: (1035, 1200), # Ashley: 5:15 PM to 8:00 PM
        3: (540, 885),   # Ronald: 9:00 AM to 2:45 PM (adjusted for start time)
        4: (795, 1215),  # William: 1:15 PM to 8:15 PM
        5: (540, 675)    # Daniel: 9:00 AM to 11:15 AM (adjusted for start time)
    }
    
    # Minimum durations for each meeting (in minutes) for events 0 to 5
    min_durations = [0, 30, 105, 90, 15, 105]
    
    # Names for events 1 to 5
    names = {
        1: "Jessica",
        2: "Ashley",
        3: "Ronald",
        4: "William",
        5: "Daniel"
    }
    
    # Create Z3 variables
    meet_vars = [None]  # for event0, not used
    start_vars = [Int(f'start_{i}') for i in range(6)]
    end_vars = [Int(f'end_{i}') for i in range(6)]
    for i in range(1, 6):
        meet_vars.append(Bool(f'meet_{i}'))
    
    # Create solver and add constraints
    s = Optimize()
    
    # Event0: fixed at Presidio at 9:00 AM (540 minutes)
    s.add(start_vars[0] == 540)
    s.add(end_vars[0] == 540)
    
    # Constraints for events 1 to 5
    for i in range(1, 6):
        # If meeting i is scheduled, then it must be within the window and meet the duration
        s.add(Implies(meet_vars[i], start_vars[i] >= windows[i][0]))
        s.add(Implies(meet_vars[i], end_vars[i] <= windows[i][1]))
        s.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + min_durations[i]))
        # Also, ensure the start and end times are non-negative and ordered
        s.add(Implies(meet_vars[i], start_vars[i] >= 0))
        s.add(Implies(meet_vars[i], end_vars[i] >= start_vars[i]))
    
    # Constraints for every pair of distinct events (i, j) with i < j
    for i in range(6):
        for j in range(i+1, 6):
            # Condition: both events are active
            if i == 0:
                active_i = BoolVal(True)
            else:
                active_i = meet_vars[i]
            if j == 0:
                active_j = BoolVal(True)
            else:
                active_j = meet_vars[j]
            condition = And(active_i, active_j)
            
            # Travel time from i to j and j to i
            travel_ij = travel[i][j]
            travel_ji = travel[j][i]
            
            # Disjunctive constraint: either i before j or j before i
            c1 = (end_vars[i] + travel_ij <= start_vars[j])
            c2 = (end_vars[j] + travel_ji <= start_vars[i])
            s.add(Implies(condition, Or(c1, c2)))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(1, 6)])
    s.maximize(total_meetings)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        meetings = []
        for i in range(1, 6):
            if is_true(model.eval(meet_vars[i])):
                start_val = model.eval(start_vars[i]).as_long()
                end_val = model.eval(end_vars[i]).as_long()
                # Convert minutes to HH:MM
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                meetings.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start_time'])
        # Output as JSON
        print('SOLUTION:')
        print(f'{{"itinerary": {meetings}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()