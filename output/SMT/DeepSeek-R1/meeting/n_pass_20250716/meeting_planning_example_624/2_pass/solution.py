from z3 import *

def main():
    # Define travel_time matrix (8x8)
    travel = [
        [0, 24, 13, 23, 10, 24, 19, 7],   # from Golden Gate Park (0)
        [25, 0, 26, 12, 20, 6, 7, 22],    # from Fisherman's Wharf (1)
        [11, 24, 0, 20, 8, 20, 18, 6],    # from The Castro (2)
        [23, 8, 22, 0, 17, 3, 7, 19],     # from Chinatown (3)
        [9, 19, 8, 16, 0, 15, 13, 5],     # from Alamo Square (4)
        [22, 5, 22, 6, 16, 0, 4, 18],     # from North Beach (5)
        [21, 7, 21, 9, 15, 5, 0, 17],     # from Russian Hill (6)
        [7, 23, 6, 19, 5, 19, 17, 0]      # from Haight-Ashbury (7)
    ]
    
    # Event data: [location, duration, available_start, available_end]
    events = [
        (0, 0, 0, 0),          # event0: start at Golden Gate Park
        (1, 60, 165, 750),     # event1: Laura (Fisherman's Wharf)
        (2, 75, 0, 300),       # event2: Karen (The Castro)
        (3, 75, 195, 750),     # event3: Elizabeth (Chinatown)
        (4, 105, 180, 360),    # event4: Deborah (Alamo Square)
        (5, 90, 345, 600),     # event5: Jason (North Beach)
        (6, 120, 345, 570),    # event6: Steven (Russian Hill)
        (7, 60, 750, 810)      # event7: Carol (Haight-Ashbury)
    ]
    
    n_events = len(events)
    loc = [event[0] for event in events]
    dur = [event[1] for event in events]
    available_start = [event[2] for event in events]
    available_end = [event[3] for event in events]
    
    # Z3 variables for start times of each event
    start = [Int(f'start_{i}') for i in range(n_events)]
    
    s = Solver()
    
    # Fix the start event (event0) at time 0
    s.add(start[0] == 0)
    
    # Fix Carol's meeting (event7) to start at 750 minutes
    s.add(start[7] == 750)
    
    # Constraints for each event (except event0 and event7 which are fixed)
    for i in range(1, n_events - 1):  # events 1 to 6
        s.add(start[i] >= available_start[i])
        s.add(start[i] + dur[i] <= available_end[i])
    
    # Additional constraints for events 1 to 6 to account for travel from start (Golden Gate Park)
    for i in range(1, n_events - 1):
        s.add(start[i] >= travel[0][loc[i]])
    
    # Disjunctive constraints for every pair of events
    for i in range(n_events):
        for j in range(i + 1, n_events):
            time_ij = travel[loc[i]][loc[j]]
            time_ji = travel[loc[j]][loc[i]]
            constraint1 = (start[i] + dur[i] + time_ij <= start[j])
            constraint2 = (start[j] + dur[j] + time_ji <= start[i])
            s.add(Or(constraint1, constraint2))
    
    # Check for satisfiability
    if s.check() == sat:
        m = s.model()
        # Collect and sort the schedule
        schedule = []
        friend_names = ["Start", "Laura", "Karen", "Elizabeth", "Deborah", "Jason", "Steven", "Carol"]
        for i in range(1, n_events):  # Skip event0 (start)
            t = m.evaluate(start[i])
            if isinstance(t, IntNumRef):
                t_val = t.as_long()
            else:
                t_val = t
            hours = 9 + t_val // 60
            minutes = t_val % 60
            end_time = t_val + dur[i]
            end_hours = 9 + end_time // 60
            end_minutes = end_time % 60
            schedule.append((friend_names[i], f"{hours}:{minutes:02d}", f"{end_hours}:{end_minutes:02d}"))
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        print("SOLUTION: Met 7 friends.")
        for name, st, et in schedule:
            print(f"Meet {name} from {st} to {et}")
    else:
        print("SOLUTION: No valid schedule found for 7 friends.")

if __name__ == "__main__":
    main()