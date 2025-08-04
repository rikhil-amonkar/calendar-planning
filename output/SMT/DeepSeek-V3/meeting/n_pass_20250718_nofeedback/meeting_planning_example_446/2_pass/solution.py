from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define districts and their indices for easier reference
    districts = {
        "Richmond District": 0,
        "Marina District": 1,
        "Chinatown": 2,
        "Financial District": 3,
        "Bayview": 4,
        "Union Square": 5
    }

    # Travel times matrix (districts x districts)
    travel_times = [
        [0, 9, 20, 22, 26, 21],   # Richmond District
        [11, 0, 16, 17, 27, 16],   # Marina District
        [20, 12, 0, 5, 22, 7],     # Chinatown
        [21, 15, 5, 0, 19, 9],     # Financial District
        [25, 25, 18, 19, 0, 17],   # Bayview
        [20, 18, 7, 9, 15, 0]      # Union Square
    ]

    # Friends' data: name, district, start_availability, end_availability, min_duration (minutes)
    friends = [
        ("Kimberly", districts["Marina District"], 13*60 + 15, 16*60 + 45, 15),
        ("Robert", districts["Chinatown"], 12*60 + 15, 20*60 + 15, 15),
        ("Rebecca", districts["Financial District"], 13*60 + 15, 16*60 + 45, 75),
        ("Margaret", districts["Bayview"], 9*60 + 30, 13*60 + 30, 30),
        ("Kenneth", districts["Union Square"], 19*60 + 30, 21*60 + 15, 75)
    ]

    # Variables for each meeting: start, end, and whether the meeting is scheduled
    meet_vars = []
    for i, (name, district, start_avail, end_avail, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        scheduled = Bool(f'scheduled_{name}')
        meet_vars.append((name, district, start, end, scheduled, start_avail, end_avail, min_dur))

    # Current time starts at 9:00 AM in Richmond District (540 minutes)
    current_time = Int('current_time')
    s.add(current_time == 9 * 60)

    # Current district starts at Richmond District
    current_district = Int('current_district')
    s.add(current_district == districts["Richmond District"])

    # For each friend, add constraints if they are scheduled
    for i, (name, district, start, end, scheduled, start_avail, end_avail, min_dur) in enumerate(meet_vars):
        # Constraints if the meeting is scheduled
        s.add(Implies(scheduled, start >= start_avail))
        s.add(Implies(scheduled, end <= end_avail))
        s.add(Implies(scheduled, end == start + min_dur))
        # The meeting must start after current_time + travel time from current_district to district
        # To handle the travel time, we need to map the current_district and district to the travel time
        # Since current_district is a Z3 variable, we cannot directly index the travel_times matrix
        # Instead, we can use a function to map the districts to their travel times
        # Here, we'll use a lookup table approach
        travel_time = Int(f'travel_{name}')
        # Create a condition for each possible current_district
        for src in districts.values():
            for dst in districts.values():
                if src == current_district and dst == district:
                    s.add(Implies(And(current_district == src, scheduled), travel_time == travel_times[src][dst]))
        s.add(Implies(scheduled, start >= current_time + travel_time))
        # Update current_time and current_district if scheduled
        new_current_time = Int(f'new_current_time_{name}')
        s.add(Implies(scheduled, new_current_time == end))
        new_current_district = Int(f'new_current_district_{name}')
        s.add(Implies(scheduled, new_current_district == district))
        # Update the current_time and current_district for the next iteration
        current_time = If(scheduled, new_current_time, current_time)
        current_district = If(scheduled, new_current_district, current_district)

    # We want to meet as many friends as possible. Let's set the objective to maximize the number of scheduled meetings.
    num_meetings = Int('num_meetings')
    s.add(num_meetings == Sum([If(scheduled, 1, 0) for (name, district, start, end, scheduled, start_avail, end_avail, min_dur) in meet_vars]))

    # Maximize the number of meetings
    s.maximize(num_meetings)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []

        # Helper function to add meeting to itinerary
        def add_meeting_if_scheduled(name, start_var, end_var, scheduled_var):
            if m.evaluate(scheduled_var):
                start = m.evaluate(start_var)
                end = m.evaluate(end_var)
                start_hour = start.as_long() // 60
                start_min = start.as_long() % 60
                end_hour = end.as_long() // 60
                end_min = end.as_long() % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hour:02d}:{start_min:02d}",
                    "end_time": f"{end_hour:02d}:{end_min:02d}"
                })

        for name, district, start, end, scheduled, start_avail, end_avail, min_dur in meet_vars:
            add_meeting_if_scheduled(name, start, end, scheduled)

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))