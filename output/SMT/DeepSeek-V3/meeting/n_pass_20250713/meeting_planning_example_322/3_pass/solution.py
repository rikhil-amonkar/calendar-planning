from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Location mapping to integers
    loc_map = {
        "Sunset": 0,
        "Russian Hill": 1,
        "Chinatown": 2,
        "Presidio": 3,
        "Fisherman's Wharf": 4
    }
    
    # Travel times matrix (in minutes)
    travel_times = {
        (0, 1): 24,   # Sunset to Russian Hill
        (0, 2): 30,   # Sunset to Chinatown
        (0, 3): 16,   # Sunset to Presidio
        (0, 4): 29,   # Sunset to Fisherman's Wharf
        (1, 0): 23,   # Russian Hill to Sunset
        (1, 2): 9,    # Russian Hill to Chinatown
        (1, 3): 14,   # Russian Hill to Presidio
        (1, 4): 7,    # Russian Hill to Fisherman's Wharf
        (2, 0): 29,   # Chinatown to Sunset
        (2, 1): 7,    # Chinatown to Russian Hill
        (2, 3): 19,   # Chinatown to Presidio
        (2, 4): 8,    # Chinatown to Fisherman's Wharf
        (3, 0): 15,   # Presidio to Sunset
        (3, 1): 14,   # Presidio to Russian Hill
        (3, 2): 21,   # Presidio to Chinatown
        (3, 4): 19,   # Presidio to Fisherman's Wharf
        (4, 0): 27,   # Fisherman's Wharf to Sunset
        (4, 1): 7,    # Fisherman's Wharf to Russian Hill
        (4, 2): 12,   # Fisherman's Wharf to Chinatown
        (4, 3): 17,   # Fisherman's Wharf to Presidio
    }

    # Friend data: name, location, available start, available end, min duration
    friends = [
        ("William", "Russian Hill", 18*60 + 30, 20*60 + 45, 105),
        ("Michelle", "Chinatown", 8*60 + 15, 14*60, 15),
        ("George", "Presidio", 10*60 + 30, 18*60 + 45, 30),
        ("Robert", "Fisherman's Wharf", 9*60, 13*60 + 45, 30),
    ]

    # Current location starts at Sunset at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = loc_map["Sunset"]

    # Variables for each friend: start time, end time
    meet_vars = []
    for name, loc, avail_start, avail_end, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet_vars.append((name, loc_map[loc], start, end, avail_start, avail_end, min_dur))

    # Constraints for each friend
    for name, loc, start, end, avail_start, avail_end, min_dur in meet_vars:
        s.add(start >= avail_start)
        s.add(end <= avail_end)
        s.add(end == start + min_dur)

    # Variables to represent the order of meetings
    order = [Int(f'order_{i}') for i in range(len(friends))]
    s.add(Distinct(order))
    for i in range(len(friends)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(friends))

    # Variables for the start and end times of each meeting in the order
    ordered_starts = [Int(f'ordered_start_{i}') for i in range(len(friends))]
    ordered_ends = [Int(f'ordered_end_{i}') for i in range(len(friends))]
    ordered_locs = [Int(f'ordered_loc_{i}') for i in range(len(friends))]

    # Map the order to the actual meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            s.add(Implies(order[i] == j,
                          And(ordered_starts[i] == meet_vars[j][2],
                              ordered_ends[i] == meet_vars[j][3],
                              ordered_locs[i] == meet_vars[j][1])))

    # Travel time constraints between consecutive meetings
    for i in range(len(friends) - 1):
        from_loc = ordered_locs[i]
        to_loc = ordered_locs[i+1]
        travel_time = travel_times[(from_loc, to_loc)]
        s.add(ordered_starts[i+1] >= ordered_ends[i] + travel_time)

    # First meeting must be after travel from Sunset
    first_loc = ordered_locs[0]
    travel_time = travel_times[(current_loc, first_loc)]
    s.add(ordered_starts[0] >= current_time + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        print("SOLUTION: Can meet all friends with the following schedule:")
        
        # Get the meeting order
        meeting_order = []
        for i in range(len(friends)):
            meeting_order.append(m[order[i]].as_long())
        
        # Print meetings in order
        for i in meeting_order:
            name, loc_num, start, end, _, _, _ = meet_vars[i]
            loc_name = [k for k, v in loc_map.items() if v == loc_num][0]
            start_time = m[start].as_long()
            end_time = m[end].as_long()
            print(f"Meet {name} at {loc_name} from {start_time//60:02d}:{start_time%60:02d} to {end_time//60:02d}:{end_time%60:02d}")
    else:
        print("No feasible schedule found to meet all friends.")

solve_scheduling()