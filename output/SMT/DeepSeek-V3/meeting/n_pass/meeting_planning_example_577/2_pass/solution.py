from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their indices for easy reference
    locations = {
        "Haight-Ashbury": 0,
        "Russian Hill": 1,
        "Fisherman's Wharf": 2,
        "Nob Hill": 3,
        "Golden Gate Park": 4,
        "Alamo Square": 5,
        "Pacific Heights": 6
    }

    # Travel time matrix (from_location_index, to_location_index) -> minutes
    travel_times = [
        [0, 17, 23, 15, 7, 5, 12],    # Haight-Ashbury to others
        [17, 0, 7, 5, 21, 15, 7],      # Russian Hill to others
        [22, 7, 0, 11, 25, 20, 12],    # Fisherman's Wharf to others
        [13, 5, 11, 0, 17, 11, 8],     # Nob Hill to others
        [7, 19, 24, 20, 0, 10, 16],    # Golden Gate Park to others
        [5, 13, 19, 11, 9, 0, 10],    # Alamo Square to others
        [11, 7, 13, 8, 15, 10, 0]     # Pacific Heights to others
    ]

    # Friends' data: name, location, available start, available end, min duration (minutes)
    friends = [
        ("Stephanie", "Russian Hill", (20, 0), (20, 45), 15),
        ("Kevin", "Fisherman's Wharf", (19, 15), (21, 45), 75),
        ("Robert", "Nob Hill", (7, 45), (10, 30), 90),
        ("Steven", "Golden Gate Park", (8, 30), (17, 0), 75),
        ("Anthony", "Alamo Square", (7, 45), (19, 45), 15),
        ("Sandra", "Pacific Heights", (14, 45), (21, 45), 45)
    ]

    # Convert time tuples to minutes since 00:00 for easier handling
    def time_to_minutes(hh_mm):
        return hh_mm[0] * 60 + hh_mm[1]

    # Convert minutes back to HH:MM string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = locations["Haight-Ashbury"]

    # Define variables for each meeting's start and end times
    meet_vars = []
    for friend in friends:
        name, loc, start_avail, end_avail, min_dur = friend
        start_avail_min = time_to_minutes(start_avail)
        end_avail_min = time_to_minutes(end_avail)
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= start_avail_min)
        s.add(end <= end_avail_min)
        s.add(end == start + min_dur)
        meet_vars.append((name, loc, start, end))

    # Define the order of meetings as a permutation
    # We'll try all possible permutations to find a feasible schedule
    # For simplicity, we'll limit to a reasonable number of permutations
    # Here, we'll try meeting Robert, Steven, Anthony, Sandra, Kevin, Stephanie
    order = ["Robert", "Steven", "Anthony", "Sandra", "Kevin", "Stephanie"]
    ordered_meets = []
    for name in order:
        for meet in meet_vars:
            if meet[0] == name:
                ordered_meets.append(meet)
                break

    # Add constraints for travel times between meetings
    prev_end = current_time
    prev_loc = current_location
    for i, (name, loc, start, end) in enumerate(ordered_meets):
        loc_idx = locations[loc]
        travel_time = travel_times[prev_loc][loc_idx]
        s.add(start >= prev_end + travel_time)
        prev_end = end
        prev_loc = loc_idx

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, loc, start, end in ordered_meets:
            start_val = model[start].as_long()
            end_val = model[end].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        # If the first order fails, try a different order
        # For example, try meeting Robert, Anthony, Steven, Sandra, Kevin, Stephanie
        s.reset()
        for friend in friends:
            name, loc, start_avail, end_avail, min_dur = friend
            start_avail_min = time_to_minutes(start_avail)
            end_avail_min = time_to_minutes(end_avail)
            start = Int(f'start_{name}')
            end = Int(f'end_{name}')
            s.add(start >= start_avail_min)
            s.add(end <= end_avail_min)
            s.add(end == start + min_dur)
            meet_vars.append((name, loc, start, end))

        order = ["Robert", "Anthony", "Steven", "Sandra", "Kevin", "Stephanie"]
        ordered_meets = []
        for name in order:
            for meet in meet_vars:
                if meet[0] == name:
                    ordered_meets.append(meet)
                    break

        prev_end = current_time
        prev_loc = current_location
        for i, (name, loc, start, end) in enumerate(ordered_meets):
            loc_idx = locations[loc]
            travel_time = travel_times[prev_loc][loc_idx]
            s.add(start >= prev_end + travel_time)
            prev_end = end
            prev_loc = loc_idx

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name, loc, start, end in ordered_meets:
                start_val = model[start].as_long()
                end_val = model[end].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Execute the solver
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))