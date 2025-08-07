from z3 import *

# Travel times dictionary
travel_time_dict = {
    "Richmond": {
        "Sunset": 11,
        "Haight-Ashbury": 10,
        "Mission": 20,
        "Golden Gate Park": 9
    },
    "Sunset": {
        "Richmond": 12,
        "Haight-Ashbury": 15,
        "Mission": 24,
        "Golden Gate Park": 11
    },
    "Haight-Ashbury": {
        "Richmond": 10,
        "Sunset": 15,
        "Mission": 11,
        "Golden Gate Park": 7
    },
    "Mission": {
        "Richmond": 20,
        "Sunset": 24,
        "Haight-Ashbury": 12,
        "Golden Gate Park": 17
    },
    "Golden Gate Park": {
        "Richmond": 7,
        "Sunset": 10,
        "Haight-Ashbury": 7,
        "Mission": 17
    }
}

# Meetings data: (name, location, min_duration, available_start, available_end in minutes from 9:00 AM)
meetings = [
    ("Sarah", "Sunset", 30, 105, 600),
    ("Richard", "Haight-Ashbury", 90, 165, 405),
    ("Elizabeth", "Mission", 120, 120, 495),
    ("Michelle", "Golden Gate Park", 90, 555, 705)
]

# Create the solver
s = Optimize()

# Variables for each meeting: meet, start, end, position
meet_flags = [Bool(f"meet_{name}") for name, _, _, _, _ in meetings]
start_vars = [Int(f"start_{name}") for name, _, _, _, _ in meetings]
end_vars = [Int(f"end_{name}") for name, _, _, _, _ in meetings]
position_vars = [Int(f"pos_{name}") for name, _, _, _, _ in meetings]

# Add constraints for each meeting
for idx, (name, loc, dur, avail_start, avail_end) in enumerate(meetings):
    # If meeting is scheduled, enforce constraints
    s.add(If(meet_flags[idx],
        And(
            start_vars[idx] >= travel_time_dict["Richmond"][loc],
            start_vars[idx] >= avail_start,
            end_vars[idx] == start_vars[idx] + dur,
            end_vars[idx] <= avail_end,
            position_vars[idx] >= 0,
            position_vars[idx] <= 3
        ),
        And(
            position_vars[idx] == 4
        )
    ))

# Distinct positions for scheduled meetings
for i in range(len(meetings)):
    for j in range(i+1, len(meetings)):
        s.add(If(And(meet_flags[i], meet_flags[j]),
            position_vars[i] != position_vars[j],
            True
        ))

# Disjunctive constraints for scheduled meetings
for i in range(len(meetings)):
    for j in range(len(meetings)):
        if i == j:
            continue
        loc_i = meetings[i][1]
        loc_j = meetings[j][1]
        travel_time_ij = travel_time_dict[loc_i][loc_j]
        travel_time_ji = travel_time_dict[loc_j][loc_i]
        s.add(If(And(meet_flags[i], meet_flags[j]),
            Or(
                And(position_vars[i] < position_vars[j], 
                    start_vars[j] >= end_vars[i] + travel_time_ij),
                And(position_vars[j] < position_vars[i], 
                    start_vars[i] >= end_vars[j] + travel_time_ji)
            ),
            True
        ))

# Maximize the number of meetings
total_meet = Sum([If(flag, 1, 0) for flag in meet_flags])
s.maximize(total_meet)

# Check for a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for idx, (name, _, dur, _, _) in enumerate(meetings):
        if model.eval(meet_flags[idx]):
            start_val = model.eval(start_vars[idx]).as_long()
            end_val = start_val + dur
            # Convert start time to HH:MM format
            hour = 9 + start_val // 60
            minute = start_val % 60
            start_time = f"{hour:02d}:{minute:02d}"
            # Convert end time to HH:MM format
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(f"SOLUTION: {{\"itinerary\": {itinerary}}}")
else:
    print("SOLUTION: {\"itinerary\": []}")