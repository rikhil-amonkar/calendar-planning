from z3 import *

def min_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{int(h):02d}:{int(m):02d}"

def main():
    # Index: 0: Karen (Fisherman's Wharf), 1: Anthony (Financial District), 2: Betty (Embarcadero)
    names = ["Karen", "Anthony", "Betty"]
    locations = ["Fisherman's Wharf", "Financial District", "Embarcadero"]
    durations = [30, 105, 15]
    
    # Travel times from Bayview to each location: [K, A, B]
    start_travel = [25, 19, 19]
    
    # Travel time matrix: T[i][j] = time from location i to j
    T = [
        [0, 11, 8],   # from K (0) to [K, A, B]
        [10, 0, 4],   # from A (1) to [K, A, B]
        [6, 5, 0]     # from B (2) to [K, A, B]
    ]
    
    # Start time in minutes (9:00 AM)
    start_time = 540
    
    # Availability constraints
    # Karen: 8:45 AM (525) to 3:00 PM (900)
    # Anthony: 9:15 AM (555) to 9:30 PM (1290)
    # Betty: 7:45 PM (1185) to 9:45 PM (1305)
    avail_min = [525, 555, 1185]
    avail_max = [900, 1290, 1305]
    
    # Create solver
    s = Solver()
    
    # Variables for start times and positions
    S = [Int(f'S_{i}') for i in range(3)]
    Pos = [Int(f'Pos_{i}') for i in range(3)]
    
    # End times
    E = [S[i] + durations[i] for i in range(3)]
    
    # Position constraints: each position between 0 and 2, and distinct
    for i in range(3):
        s.add(Pos[i] >= 0, Pos[i] <= 2)
    s.add(Distinct(Pos[0], Pos[1], Pos[2]))
    
    # Availability constraints
    for i in range(3):
        s.add(S[i] >= avail_min[i])
        s.add(E[i] <= avail_max[i])
    
    # First meeting constraint: if meeting i is first, then S[i] >= start_time + start_travel[i]
    for i in range(3):
        s.add(If(Pos[i] == 0, S[i] >= start_time + start_travel[i], True))
    
    # Sequence constraints: if meeting i is before j, then S[j] >= E[i] + T[i][j]
    for i in range(3):
        for j in range(3):
            if i != j:
                s.add(If(Pos[i] < Pos[j], S[j] >= E[i] + T[i][j], True))
    
    # Check and get solution
    if s.check() == sat:
        m = s.model()
        start_times = [m.evaluate(S[i]).as_long() for i in range(3)]
        positions = [m.evaluate(Pos[i]).as_long() for i in range(3)]
        
        # Determine schedule order
        schedule_order = []
        for pos_val in range(3):
            for i in range(3):
                if positions[i] == pos_val:
                    schedule_order.append(i)
        
        # Build schedule
        result = []
        result.append("Start at Bayview at 09:00")
        
        # First meeting
        first = schedule_order[0]
        travel_start = start_travel[first]
        arrival_first = start_time + travel_start
        result.append(f"  Travel to {locations[first]} for {travel_start} minutes, arriving at {min_to_time(arrival_first)}")
        result.append(f"  Meet {names[first]} at {locations[first]} from {min_to_time(start_times[first])} to {min_to_time(start_times[first] + durations[first])}")
        
        # Subsequent meetings
        for idx in range(1, 3):
            prev = schedule_order[idx-1]
            curr = schedule_order[idx]
            travel_time = T[prev][curr]
            leave_prev = start_times[prev] + durations[prev]
            arrive_curr = leave_prev + travel_time
            result.append(f"  Travel from {locations[prev]} to {locations[curr]} for {travel_time} minutes, arriving at {min_to_time(arrive_curr)}")
            result.append(f"  Meet {names[curr]} at {locations[curr]} from {min_to_time(start_times[curr])} to {min_to_time(start_times[curr] + durations[curr])}")
        
        print("SOLUTION:")
        print('\n'.join(result))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()