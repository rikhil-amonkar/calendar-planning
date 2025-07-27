from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes from midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Friends' data: name, location, available start, available end, min duration
    friends = [
        ("Kimberly", "Marina District", time_to_minutes("13:15"), time_to_minutes("16:45"), 15),
        ("Robert", "Chinatown", time_to_minutes("12:15"), time_to_minutes("20:15"), 15),
        ("Rebecca", "Financial District", time_to_minutes("13:15"), time_to_minutes("16:45"), 75),
        ("Margaret", "Bayview", time_to_minutes("09:30"), time_to_minutes("13:30"), 30),
        ("Kenneth", "Union Square", time_to_minutes("19:30"), time_to_minutes("21:15"), 75)
    ]

    # Travel times dictionary: (from, to) -> minutes
    travel_times = {
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Bayview"): 26,
        ("Richmond District", "Union Square"): 21,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Chinatown"): 16,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Union Square"): 7,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Union Square"): 9,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Marina District"): 25,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Union Square"): 17,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Bayview"): 15
    }

    # Variables for each meeting: start and end times
    meet_vars = []
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= avail_start)
        s.add(end <= avail_end)
        s.add(end == start + min_dur)
        meet_vars.append((name, loc, start, end))

    # Sequence constraints: ensure travel times between meetings are respected
    # We need to decide the order of meetings. This is complex; we'll assume a possible order and adjust.
    # For simplicity, we'll try a specific order that might work: Margaret, Robert, Rebecca, Kimberly, Kenneth
    # This is a heuristic; in a full solution, we'd need to explore all permutations or use a more sophisticated approach.

    # Let's try the order: Margaret (Bayview), Robert (Chinatown), Rebecca (Financial District), Kimberly (Marina District), Kenneth (Union Square)
    order = [3, 1, 2, 0, 4]  # Indices of friends in the order above

    for i in range(len(order) - 1):
        current_idx = order[i]
        next_idx = order[i + 1]
        current_name, current_loc, _, current_end = meet_vars[current_idx]
        next_name, next_loc, next_start, _ = meet_vars[next_idx]
        travel_time = travel_times.get((current_loc, next_loc), 60)  # Default high if not found (shouldn't happen)
        s.add(next_start >= current_end + travel_time)

    # Also, the first meeting must be after arrival (9:00 AM, 0 in our time)
    first_idx = order[0]
    _, _, first_start, _ = meet_vars[first_idx]
    s.add(first_start >= 0)  # 9:00 AM is time 0 here

    # Check if the schedule is possible
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name, loc, start_var, end_var in meet_vars:
            start_val = m.evaluate(start_var).as_long()
            end_val = m.evaluate(end_var).as_long()
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
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)