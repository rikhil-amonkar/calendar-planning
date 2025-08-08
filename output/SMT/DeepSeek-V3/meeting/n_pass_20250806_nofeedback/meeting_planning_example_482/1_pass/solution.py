from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        "Haight-Ashbury": 0,
        "Mission District": 1,
        "Bayview": 2,
        "Pacific Heights": 3,
        "Russian Hill": 4,
        "Fisherman's Wharf": 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 11, 18, 12, 17, 23],  # Haight-Ashbury to others
        [12, 0, 15, 16, 15, 22],   # Mission District to others
        [19, 13, 0, 23, 23, 25],    # Bayview to others
        [11, 15, 22, 0, 7, 13],     # Pacific Heights to others
        [17, 16, 23, 7, 0, 7],      # Russian Hill to others
        [22, 22, 26, 12, 7, 0]      # Fisherman's Wharf to others
    ]

    # Friends' data: name, location, available start, available end, min duration
    friends = [
        ("Stephanie", 1, 8*60 + 15, 13*60 + 45, 90),
        ("Sandra", 2, 13*60 + 0, 19*60 + 30, 15),
        ("Richard", 3, 7*60 + 15, 10*60 + 15, 75),
        ("Brian", 4, 12*60 + 15, 16*60 + 0, 120),
        ("Jason", 5, 8*60 + 30, 17*60 + 45, 60)
    ]

    # Variables for each meeting: start and end times (in minutes since midnight)
    meet_vars = []
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= avail_start)
        s.add(end <= avail_end)
        s.add(end == start + min_dur)
        meet_vars.append((name, loc, start, end))

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = 0  # Haight-Ashbury

    # Order of meetings (we'll let Z3 decide the order)
    order = [Int(f'order_{i}') for i in range(len(friends))]
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 0, o < len(friends))

    # Constraints for travel times and meeting order
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If meeting i is before meeting j, then meeting j must start after meeting i ends plus travel time
                name_i, loc_i, start_i, end_i = meet_vars[i]
                name_j, loc_j, start_j, end_j = meet_vars[j]
                s.add(Implies(order[i] < order[j], start_j >= end_i + travel_times[loc_i][loc_j]))

    # First meeting must start after current time plus travel time from current location
    for i in range(len(friends)):
        name, loc, start, end = meet_vars[i]
        s.add(Implies(order[i] == 0, start >= current_time + travel_times[current_loc][loc]))

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        # Get the order of meetings
        meeting_order = sorted([(i, m.evaluate(order[i]).as_long()) for i in range(len(friends))], key=lambda x: x[1])
        # Build the itinerary
        itinerary = []
        for i, pos in meeting_order:
            name, loc, start, end = meet_vars[i]
            start_time = m.evaluate(start).as_long()
            end_time = m.evaluate(end).as_long()
            # Convert minutes to HH:MM format
            start_hh = start_time // 60
            start_mm = start_time % 60
            end_hh = end_time // 60
            end_mm = end_time % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))