from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Locations
    locations = ["Sunset", "Russian Hill", "Chinatown", "Presidio", "Fisherman's Wharf"]
    
    # Travel times matrix (in minutes)
    travel_times = {
        ("Sunset", "Russian Hill"): 24,
        ("Sunset", "Chinatown"): 30,
        ("Sunset", "Presidio"): 16,
        ("Sunset", "Fisherman's Wharf"): 29,
        ("Russian Hill", "Sunset"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Chinatown", "Sunset"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Presidio", "Sunset"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Fisherman's Wharf", "Sunset"): 27,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Presidio"): 17,
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
    current_loc = "Sunset"

    # Variables for each friend: start time, end time, and whether they are met
    meet_vars = []
    for name, loc, avail_start, avail_end, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        met = Bool(f'met_{name}')
        meet_vars.append((name, loc, start, end, met, avail_start, avail_end, min_dur))

    # Constraints for each friend
    for name, loc, start, end, met, avail_start, avail_end, min_dur in meet_vars:
        # If met, then start and end must be within availability and duration >= min_dur
        s.add(Implies(met, And(start >= avail_start,
                               end <= avail_end,
                               end == start + min_dur)))
        # If not met, then start and end are unconstrained (but we'll minimize unmet friends)
        s.add(Implies(Not(met), And(start == 0, end == 0)))

    # Constraints for travel and ordering
    # We need to decide the order of meetings
    # Let's assume we can meet all friends, and let Z3 find the order
    # We'll add constraints for travel times between consecutive meetings
    # We'll use a list to represent the order of meetings
    order = [Int(f'order_{i}') for i in range(len(friends))]
    s.add(Distinct(order))
    for i in range(len(friends)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(friends))

    # Variables for the start and end times of each meeting in the order
    ordered_starts = [Int(f'ordered_start_{i}') for i in range(len(friends))]
    ordered_ends = [Int(f'ordered_end_{i}') for i in range(len(friends))]
    ordered_locs = [String(f'ordered_loc_{i}') for i in range(len(friends))]
    ordered_mets = [Bool(f'ordered_met_{i}') for i in range(len(friends))]

    # Map the order to the actual meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            s.add(Implies(order[i] == j,
                          And(ordered_starts[i] == meet_vars[j][2],
                              ordered_ends[i] == meet_vars[j][3],
                              ordered_locs[i] == meet_vars[j][1],
                              ordered_mets[i] == meet_vars[j][4])))

    # Travel time constraints between consecutive meetings
    for i in range(len(friends) - 1):
        # If both meetings are met, then the next start must be >= current end + travel time
        s.add(Implies(And(ordered_mets[i], ordered_mets[i+1]),
                       ordered_starts[i+1] >= ordered_ends[i] + travel_times[(ordered_locs[i], ordered_locs[i+1])]))

    # First meeting must be after travel from Sunset
    s.add(Implies(ordered_mets[0],
                  ordered_starts[0] >= current_time + travel_times[(current_loc, ordered_locs[0])]))

    # Maximize the number of friends met
    num_met = Int('num_met')
    s.add(num_met == Sum([If(met, 1, 0) for name, loc, start, end, met, avail_start, avail_end, min_dur in meet_vars]))
    maximize_num_met = num_met == len(friends)  # Try to meet all friends first

    # Check if we can meet all friends
    s.push()
    s.add(maximize_num_met)
    if s.check() == sat:
        m = s.model()
        print("SOLUTION: Can meet all friends with the following schedule:")
        for name, loc, start, end, met, avail_start, avail_end, min_dur in meet_vars:
            if m[met]:
                start_time = m[start].as_long()
                end_time = m[end].as_long()
                print(f"Meet {name} at {loc} from {start_time//60:02d}:{start_time%60:02d} to {end_time//60:02d}:{end_time%60:02d}")
    else:
        s.pop()
        # If not, try to maximize the number of friends met
        s.add(num_met >= 3)  # Try to meet at least 3 friends
        if s.check() == sat:
            m = s.model()
            print("SOLUTION: Can meet 3 friends with the following schedule:")
            for name, loc, start, end, met, avail_start, avail_end, min_dur in meet_vars:
                if m[met]:
                    start_time = m[start].as_long()
                    end_time = m[end].as_long()
                    print(f"Meet {name} at {loc} from {start_time//60:02d}:{start_time%60:02d} to {end_time//60:02d}:{end_time%60:02d}")
        else:
            print("No feasible schedule found.")

solve_scheduling()