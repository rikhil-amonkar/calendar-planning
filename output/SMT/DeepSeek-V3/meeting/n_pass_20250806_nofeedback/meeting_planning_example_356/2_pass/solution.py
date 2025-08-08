from z3 import *
import json

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Define friends and their constraints
    friends = [
        {
            "name": "Barbara",
            "location": "North Beach",
            "available_start": (13, 45),  # 1:45 PM
            "available_end": (20, 15),    # 8:15 PM
            "min_duration": 60            # minutes
        },
        {
            "name": "Margaret",
            "location": "Presidio",
            "available_start": (10, 15),  # 10:15 AM
            "available_end": (15, 15),    # 3:15 PM
            "min_duration": 30           # minutes
        },
        {
            "name": "Kevin",
            "location": "Haight-Ashbury",
            "available_start": (20, 0),   # 8:00 PM
            "available_end": (20, 45),    # 8:45 PM
            "min_duration": 30           # minutes
        },
        {
            "name": "Kimberly",
            "location": "Union Square",
            "available_start": (7, 45),    # 7:45 AM
            "available_end": (16, 45),    # 4:45 PM
            "min_duration": 30             # minutes
        }
    ]

    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        "Bayview": {
            "North Beach": 21,
            "Presidio": 31,
            "Haight-Ashbury": 19,
            "Union Square": 17
        },
        "North Beach": {
            "Bayview": 22,
            "Presidio": 17,
            "Haight-Ashbury": 18,
            "Union Square": 7
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Haight-Ashbury": 15,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Presidio": 15,
            "Union Square": 17
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Presidio": 24,
            "Haight-Ashbury": 18
        }
    }

    # Current location starts at Bayview at 9:00 AM
    current_location = "Bayview"
    current_time = (9, 0)  # 9:00 AM

    # Convert all times to minutes since midnight for easier arithmetic
    def time_to_minutes(h, m):
        return h * 60 + m

    # Convert minutes back to (h, m)
    def minutes_to_time(total):
        h = total // 60
        m = total % 60
        return (h, m)

    # Create variables for each friend's meeting start and end times (in minutes since midnight)
    meetings = []
    for friend in friends:
        start_var = Int(f'start_{friend["name"]}')
        end_var = Int(f'end_{friend["name"]}')
        duration_var = Int(f'duration_{friend["name"]}')
        opt.add(start_var >= time_to_minutes(*friend["available_start"]))
        opt.add(end_var <= time_to_minutes(*friend["available_end"]))
        opt.add(end_var == start_var + duration_var)
        opt.add(duration_var >= friend["min_duration"])
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "duration_var": duration_var
        })

    # Add constraints for travel times between meetings
    # Assume the order is Kimberly, Margaret, Barbara, Kevin
    order = ["Kimberly", "Margaret", "Barbara", "Kevin"]
    ordered_meetings = []
    for name in order:
        for m in meetings:
            if m["name"] == name:
                ordered_meetings.append(m)
                break

    # Add travel constraints between meetings
    prev_location = "Bayview"
    prev_end_time = time_to_minutes(9, 0)  # start at 9:00 AM at Bayview
    for i in range(len(ordered_meetings)):
        m = ordered_meetings[i]
        travel_time = travel_times[prev_location][m["location"]]
        opt.add(m["start_var"] >= prev_end_time + travel_time)
        prev_location = m["location"]
        prev_end_time = m["end_var"]

    # Also, ensure no overlapping meetings (though the order should prevent this)
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]
            opt.add(Or(
                m1["end_var"] <= m2["start_var"],
                m2["end_var"] <= m1["start_var"]
            ))

    # Maximize the total meeting time
    total_time = sum([m["duration_var"] for m in meetings])
    opt.maximize(total_time)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for m in meetings:
            start_val = model.eval(m["start_var"]).as_long()
            end_val = model.eval(m["end_var"]).as_long()
            start_h, start_m = minutes_to_time(start_val)
            end_h, end_m = minutes_to_time(end_val)
            itinerary.append({
                "action": "meet",
                "person": m["name"],
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:5])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))