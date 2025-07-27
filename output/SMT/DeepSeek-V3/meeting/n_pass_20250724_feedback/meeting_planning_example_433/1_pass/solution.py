from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Friends' data: name, location, available start, available end, min duration
    friends = [
        ("Emily", "Richmond District", time_to_minutes("19:00"), time_to_minutes("21:00"), 15),
        ("Margaret", "Financial District", time_to_minutes("16:30"), time_to_minutes("20:15"), 75),
        ("Ronald", "North Beach", time_to_minutes("18:30"), time_to_minutes("19:30"), 45),
        ("Deborah", "The Castro", time_to_minutes("13:45"), time_to_minutes("21:15"), 90),
        ("Jeffrey", "Golden Gate Park", time_to_minutes("11:15"), time_to_minutes("14:30"), 120)
    ]

    # Travel times dictionary: (from, to) -> minutes
    travel_times = {
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Golden Gate Park"): 23,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Financial District"): 20,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "The Castro"): 13
    }

    # Variables for each friend's meeting start and end times
    meet_vars = []
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= 0)
        s.add(end <= time_to_minutes("21:15"))  # Latest possible time
        s.add(start >= avail_start)
        s.add(end <= avail_end)
        s.add(end == start + min_dur)
        meet_vars.append((name, loc, start, end))

    # Sequence constraints: order of meetings and travel times
    # We need to find a permutation of the meetings that fits the time constraints
    # This is complex, so we'll use a simple approach: try to meet friends in order of earliest availability first
    # But since Z3 can handle this, we'll define an order and enforce travel times between consecutive meetings
    # To simplify, we'll assume an order and let Z3 find feasible start times

    # Let's define a possible order: Jeffrey, Deborah, Margaret, Ronald, Emily
    # This is based on their available times
    order = [4, 3, 1, 2, 0]  # Indices of friends in order: Jeffrey, Deborah, Margaret, Ronald, Emily

    # Add constraints for travel times between consecutive meetings
    for i in range(len(order) - 1):
        prev_idx = order[i]
        next_idx = order[i + 1]
        prev_name, prev_loc, prev_start, prev_end = meet_vars[prev_idx]
        next_name, next_loc, next_start, next_end = meet_vars[next_idx]
        travel_key = (prev_loc, next_loc)
        travel_time = travel_times[travel_key]
        s.add(next_start >= prev_end + travel_time)

    # Also, the first meeting must start after travel from Nob Hill
    first_idx = order[0]
    first_name, first_loc, first_start, first_end = meet_vars[first_idx]
    travel_time_first = travel_times[("Nob Hill", first_loc)]
    s.add(first_start >= travel_time_first)

    # Check if the solution is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, loc, start_var, end_var in meet_vars:
            start_val = model[start_var].as_long()
            end_val = model[end_var].as_long()
            start_time = minutes_to_time(start_val)
            end_time = minutes_to_time(end_val)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

result = solve_scheduling()
print(json.dumps(result, indent=2))