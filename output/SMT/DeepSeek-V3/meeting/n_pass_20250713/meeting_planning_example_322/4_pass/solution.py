from z3 import *
from itertools import permutations

def solve_scheduling():
    # Location mapping to integers
    loc_map = {
        "Sunset": 0,
        "Russian Hill": 1,
        "Chinatown": 2,
        "Presidio": 3,
        "Fisherman's Wharf": 4
    }
    
    # Travel times matrix (in minutes)
    travel_times = [
        [0, 24, 30, 16, 29],  # Sunset
        [23, 0, 9, 14, 7],     # Russian Hill
        [29, 7, 0, 19, 8],     # Chinatown
        [15, 14, 21, 0, 19],   # Presidio
        [27, 7, 12, 17, 0]     # Fisherman's Wharf
    ]

    # Friend data: name, location, available start, available end, min duration
    friends = [
        ("William", 1, 18*60 + 30, 20*60 + 45, 105),
        ("Michelle", 2, 8*60 + 15, 14*60, 15),
        ("George", 3, 10*60 + 30, 18*60 + 45, 30),
        ("Robert", 4, 9*60, 13*60 + 45, 30),
    ]

    # Current location starts at Sunset at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = 0  # Sunset

    # Generate all possible meeting orders (permutations)
    for order in permutations(range(len(friends))):
        s = Solver()
        
        # Variables for each friend's start and end times
        starts = [Int(f'start_{i}') for i in range(len(friends))]
        ends = [Int(f'end_{i}') for i in range(len(friends))]
        
        # Meeting constraints for each friend
        for i in range(len(friends)):
            name, loc, avail_start, avail_end, min_dur = friends[i]
            s.add(starts[i] >= avail_start)
            s.add(ends[i] <= avail_end)
            s.add(ends[i] == starts[i] + min_dur)
        
        # Travel time constraints between meetings
        prev_loc = current_loc
        prev_end = current_time
        
        for i in order:
            friend_loc = friends[i][1]
            travel_time = travel_times[prev_loc][friend_loc]
            
            # Arrival time at friend's location
            arrival = prev_end + travel_time
            
            # Must arrive before meeting can start
            s.add(starts[i] >= arrival)
            
            # Update for next iteration
            prev_loc = friend_loc
            prev_end = ends[i]
        
        # Check if this order is feasible
        if s.check() == sat:
            m = s.model()
            print("SOLUTION: Can meet all friends with the following schedule:")
            
            # Print meetings in order
            for i in order:
                name = friends[i][0]
                loc = [k for k, v in loc_map.items() if v == friends[i][1]][0]
                start = m[starts[i]].as_long()
                end = m[ends[i]].as_long()
                print(f"Meet {name} at {loc} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
            
            return
    
    print("No feasible schedule found to meet all friends.")

solve_scheduling()