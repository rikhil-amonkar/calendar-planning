from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define travel times matrix (from_location, to_location) -> minutes
    travel_times = {
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "The Castro"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "The Castro"): 17,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Sunset District"): 17
    }

    # Friends' availability and constraints
    friends = [
        {"name": "Richard", "location": "Embarcadero", "start": (15, 15), "end": (18, 45), "duration": 90, "priority": 1},
        {"name": "Mark", "location": "Pacific Heights", "start": (15, 0), "end": (17, 0), "duration": 45, "priority": 2},
        {"name": "Matthew", "location": "Russian Hill", "start": (17, 30), "end": (21, 0), "duration": 90, "priority": 1},
        {"name": "Rebecca", "location": "Haight-Ashbury", "start": (14, 45), "end": (18, 0), "duration": 60, "priority": 2},
        {"name": "Melissa", "location": "Golden Gate Park", "start": (13, 45), "end": (17, 30), "duration": 90, "priority": 1},
        {"name": "Margaret", "location": "Fisherman's Wharf", "start": (14, 45), "end": (20, 15), "duration": 15, "priority": 3},
        {"name": "Emily", "location": "Sunset District", "start": (15, 45), "end": (17, 0), "duration": 45, "priority": 3},
        {"name": "George", "location": "The Castro", "start": (14, 0), "end": (16, 15), "duration": 75, "priority": 2}
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total = m + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Variables for each meeting
    meeting_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        # Basic time constraints
        opt.add(start_var >= time_to_minutes(*friend['start']))
        opt.add(end_var <= time_to_minutes(*friend['end']))
        opt.add(end_var - start_var >= friend['duration'])
        meeting_vars.append((friend, start_var, end_var))

    # Order constraints with travel times
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            friend1, start1, end1 = meeting_vars[i]
            friend2, start2, end2 = meeting_vars[j]
            # Get travel time between locations
            travel_time = travel_times.get((friend1['location'], friend2['location']), 0)
            # Either meeting1 is before meeting2 with travel time, or vice versa
            opt.add(Or(
                end1 + travel_time <= start2,
                end2 + travel_times.get((friend2['location'], friend1['location']), 0) <= start1
            ))

    # Create a variable for each meeting indicating if it's scheduled
    scheduled = [Int(f"scheduled_{friend['name']}") for friend in friends]
    for i, (friend, start, end) in enumerate(meeting_vars):
        opt.add(scheduled[i] == If(end - start >= friend['duration'], friend['priority'], 0))

    # Maximize the sum of priorities of scheduled meetings
    total_priority = Int('total_priority')
    opt.add(total_priority == Sum(scheduled))
    opt.maximize(total_priority)

    # Solve the problem
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for friend, start_var, end_var in meeting_vars:
            start = model.evaluate(start_var).as_long()
            end = model.evaluate(end_var).as_long()
            if end - start >= friend['duration']:  # Only include meetings that meet duration
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the optimizer and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))