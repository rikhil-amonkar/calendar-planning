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

    # Variables to track the current district (initial: Richmond)
    current_district = Int('current_district')
    s.add(current_district == districts["Richmond District"])

    # List to store the sequence of meetings and travel
    sequence = []

    # For each friend, add constraints if they are scheduled
    for i, (name, district, start, end, scheduled, start_avail, end_avail, min_dur) in enumerate(meet_vars):
        # Constraints if the meeting is scheduled
        s.add(Implies(scheduled, start >= start_avail))
        s.add(Implies(scheduled, end <= end_avail))
        s.add(Implies(scheduled, end == start + min_dur))
        # The meeting must start after current_time + travel time
        travel_time = Int(f'travel_{name}')
        s.add(travel_time == travel_times[current_district][district])
        s.add(Implies(scheduled, start >= current_time + travel_time))
        # Update current_time and current_district if scheduled
        new_current_time = Int(f'new_current_time_{name}')
        s.add(Implies(scheduled, new_current_time == end))
        s.add(Implies(scheduled, current_district == district))
        # Add to sequence if scheduled
        sequence.append((scheduled, new_current_time, current_district, name, start, end))

    # Ensure Kenneth is met (since it's the last possible meeting)
    # To maximize the number of friends met, we can add constraints to meet as many as possible
    # For simplicity, let's assume we want to meet all possible friends, but in order.
    # Alternatively, we can set an objective to maximize the number of scheduled meetings.
    # Here, we'll proceed with meeting as many as possible in a feasible schedule.

    # For now, let's try to meet all friends in some order, respecting constraints.
    # We'll need to define the order of meetings. This is complex; instead, we'll allow the solver to choose.

    # Alternatively, we can model this as a sequence where each step chooses whether to meet a friend next.
    # This requires more complex modeling, perhaps using arrays or additional variables.

    # For this problem, let's try to meet Margaret first, then others, as it's early.

    # We'll proceed by manually setting a possible order and checking feasibility.
    # This is a heuristic approach; a more comprehensive solution would involve more complex modeling.

    # Let's try to meet Margaret, then Kimberly, Rebecca, Robert, and Kenneth.

    # Reset the solver and try a specific order.
    s = Solver()

    # Variables for each meeting
    meet_margaret = Bool('meet_margaret')
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')
    meet_kimberly = Bool('meet_kimberly')
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    meet_rebecca = Bool('meet_rebecca')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    meet_robert = Bool('meet_robert')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')
    meet_kenneth = Bool('meet_kenneth')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Initial current time and district
    current_time_var = Int('initial_time')
    s.add(current_time_var == 9 * 60)  # 9:00 AM
    current_district_var = Int('initial_district')
    s.add(current_district_var == districts["Richmond District"])

    # Margaret: Bayview, 9:30AM-1:30PM, min 30 minutes
    s.add(Implies(meet_margaret, margaret_start >= 9*60 + 30))
    s.add(Implies(meet_margaret, margaret_end <= 13*60 + 30))
    s.add(Implies(meet_margaret, margaret_end == margaret_start + 30))
    # Travel time to Bayview from Richmond: 26 minutes
    s.add(Implies(meet_margaret, margaret_start >= current_time_var + 26))
    # Update current time and district after meeting Margaret
    time_after_margaret = Int('time_after_margaret')
    s.add(Implies(meet_margaret, time_after_margaret == margaret_end))
    district_after_margaret = Int('district_after_margaret')
    s.add(Implies(meet_margaret, district_after_margaret == districts["Bayview"]))
    s.add(Implies(Not(meet_margaret), time_after_margaret == current_time_var))
    s.add(Implies(Not(meet_margaret), district_after_margaret == current_district_var))

    # Kimberly: Marina, 1:15PM-4:45PM, min 15 minutes
    s.add(Implies(meet_kimberly, kimberly_start >= 13*60 + 15))
    s.add(Implies(meet_kimberly, kimberly_end <= 16*60 + 45))
    s.add(Implies(meet_kimberly, kimberly_end == kimberly_start + 15))
    # Travel time from current district (after Margaret) to Marina
    travel_to_marina = Int('travel_to_marina')
    s.add(travel_to_marina == travel_times[district_after_margaret][districts["Marina District"]])
    s.add(Implies(meet_kimberly, kimberly_start >= time_after_margaret + travel_to_marina))
    time_after_kimberly = Int('time_after_kimberly')
    s.add(Implies(meet_kimberly, time_after_kimberly == kimberly_end))
    district_after_kimberly = Int('district_after_kimberly')
    s.add(Implies(meet_kimberly, district_after_kimberly == districts["Marina District"]))
    s.add(Implies(Not(meet_kimberly), time_after_kimberly == time_after_margaret))
    s.add(Implies(Not(meet_kimberly), district_after_kimberly == district_after_margaret))

    # Rebecca: Financial, 1:15PM-4:45PM, min 75 minutes
    s.add(Implies(meet_rebecca, rebecca_start >= 13*60 + 15))
    s.add(Implies(meet_rebecca, rebecca_end <= 16*60 + 45))
    s.add(Implies(meet_rebecca, rebecca_end == rebecca_start + 75))
    # Travel time from current district (after Kimberly) to Financial
    travel_to_financial = Int('travel_to_financial')
    s.add(travel_to_financial == travel_times[district_after_kimberly][districts["Financial District"]])
    s.add(Implies(meet_rebecca, rebecca_start >= time_after_kimberly + travel_to_financial))
    time_after_rebecca = Int('time_after_rebecca')
    s.add(Implies(meet_rebecca, time_after_rebecca == rebecca_end))
    district_after_rebecca = Int('district_after_rebecca')
    s.add(Implies(meet_rebecca, district_after_rebecca == districts["Financial District"]))
    s.add(Implies(Not(meet_rebecca), time_after_rebecca == time_after_kimberly))
    s.add(Implies(Not(meet_rebecca), district_after_rebecca == district_after_kimberly))

    # Robert: Chinatown, 12:15PM-8:15PM, min 15 minutes
    s.add(Implies(meet_robert, robert_start >= 12*60 + 15))
    s.add(Implies(meet_robert, robert_end <= 20*60 + 15))
    s.add(Implies(meet_robert, robert_end == robert_start + 15))
    # Travel time from current district (after Rebecca) to Chinatown
    travel_to_chinatown = Int('travel_to_chinatown')
    s.add(travel_to_chinatown == travel_times[district_after_rebecca][districts["Chinatown"]])
    s.add(Implies(meet_robert, robert_start >= time_after_rebecca + travel_to_chinatown))
    time_after_robert = Int('time_after_robert')
    s.add(Implies(meet_robert, time_after_robert == robert_end))
    district_after_robert = Int('district_after_robert')
    s.add(Implies(meet_robert, district_after_robert == districts["Chinatown"]))
    s.add(Implies(Not(meet_robert), time_after_robert == time_after_rebecca))
    s.add(Implies(Not(meet_robert), district_after_robert == district_after_rebecca))

    # Kenneth: Union Square, 7:30PM-9:15PM, min 75 minutes
    s.add(Implies(meet_kenneth, kenneth_start >= 19*60 + 30))
    s.add(Implies(meet_kenneth, kenneth_end <= 21*60 + 15))
    s.add(Implies(meet_kenneth, kenneth_end == kenneth_start + 75))
    # Travel time from current district (after Robert) to Union Square
    travel_to_unionsquare = Int('travel_to_unionsquare')
    s.add(travel_to_unionsquare == travel_times[district_after_robert][districts["Union Square"]])
    s.add(Implies(meet_kenneth, kenneth_start >= time_after_robert + travel_to_unionsquare))
    time_after_kenneth = Int('time_after_kenneth')
    s.add(Implies(meet_kenneth, time_after_kenneth == kenneth_end))
    district_after_kenneth = Int('district_after_kenneth')
    s.add(Implies(meet_kenneth, district_after_kenneth == districts["Union Square"]))
    s.add(Implies(Not(meet_kenneth), time_after_kenneth == time_after_robert))
    s.add(Implies(Not(meet_kenneth), district_after_kenneth == district_after_robert))

    # We want to meet as many friends as possible. Let's set the objective to maximize the number of scheduled meetings.
    num_meetings = Int('num_meetings')
    s.add(num_meetings == If(meet_margaret, 1, 0) + If(meet_kimberly, 1, 0) + If(meet_rebecca, 1, 0) + If(meet_robert, 1, 0) + If(meet_kenneth, 1, 0))

    # Maximize the number of meetings
    maximize_num_meetings = num_meetings == 5  # Try to meet all friends
    s.add(maximize_num_meetings)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []

        # Helper function to add meeting to itinerary
        def add_meeting_if_scheduled(meet_var, start_var, end_var, name):
            if m.evaluate(meet_var):
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

        add_meeting_if_scheduled(meet_margaret, margaret_start, margaret_end, "Margaret")
        add_meeting_if_scheduled(meet_kimberly, kimberly_start, kimberly_end, "Kimberly")
        add_meeting_if_scheduled(meet_rebecca, rebecca_start, rebecca_end, "Rebecca")
        add_meeting_if_scheduled(meet_robert, robert_start, robert_end, "Robert")
        add_meeting_if_scheduled(meet_kenneth, kenneth_start, kenneth_end, "Kenneth")

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))