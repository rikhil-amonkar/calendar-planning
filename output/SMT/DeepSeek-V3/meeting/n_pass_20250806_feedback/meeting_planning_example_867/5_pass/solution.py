from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define friends and their constraints
    friends = [
        {"name": "Elizabeth", "location": "Mission District", "start_avail": "10:30", "end_avail": "20:00", "min_duration": 90},
        {"name": "David", "location": "Union Square", "start_avail": "15:15", "end_avail": "19:00", "min_duration": 45},
        {"name": "Sandra", "location": "Pacific Heights", "start_avail": "07:00", "end_avail": "20:00", "min_duration": 120},
        {"name": "Thomas", "location": "Bayview", "start_avail": "19:30", "end_avail": "20:30", "min_duration": 30},
        {"name": "Robert", "location": "Fisherman's Wharf", "start_avail": "10:00", "end_avail": "15:00", "min_duration": 15},
        {"name": "Kenneth", "location": "Marina District", "start_avail": "10:45", "end_avail": "13:00", "min_duration": 45},
        {"name": "Melissa", "location": "Richmond District", "start_avail": "18:15", "end_avail": "20:00", "min_duration": 15},
        {"name": "Kimberly", "location": "Sunset District", "start_avail": "10:15", "end_avail": "18:15", "min_duration": 105},
        {"name": "Amanda", "location": "Golden Gate Park", "start_avail": "07:45", "end_avail": "18:45", "min_duration": 15}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_location = "Haight-Ashbury"
    current_time = 540  # 9:00 AM in minutes

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "min_duration": friend["min_duration"],
            "start_avail": time_to_minutes(friend["start_avail"]),
            "end_avail": time_to_minutes(friend["end_avail"])
        })

    # Add constraints for each meeting
    for meeting in meetings:
        s.add(meeting["start_var"] >= meeting["start_avail"])
        s.add(meeting["end_var"] <= meeting["end_avail"])
        s.add(meeting["end_var"] - meeting["start_var"] >= meeting["min_duration"])

    # Define travel times between locations
    travel_times = {
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Golden Gate Park"): 17,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Golden Gate Park"): 22,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Sunset District"): 21,
        ("Marina District", "Golden Gate Park"): 18,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Sunset District"): 10
    }

    # Define the order of meetings to try
    meeting_order = [
        "Amanda", "Kimberly", "Kenneth", "Robert", "Elizabeth", "David", "Sandra", "Melissa", "Thomas"
    ]

    # Add constraints for travel times between consecutive meetings
    prev_end = current_time
    prev_location = current_location
    for i in range(len(meeting_order)):
        current_meeting = next(m for m in meetings if m["name"] == meeting_order[i])
        travel_key = (prev_location, current_meeting["location"])
        travel_time = travel_times.get(travel_key, 0)
        s.add(current_meeting["start_var"] >= prev_end + travel_time)
        prev_end = current_meeting["end_var"]
        prev_location = current_meeting["location"]

    # Add soft constraints to maximize the number of meetings
    for meeting in meetings:
        s.maximize(meeting["end_var"] - meeting["start_var"])

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for meeting in meetings:
            start = m.evaluate(meeting["start_var"]).as_long()
            end = m.evaluate(meeting["end_var"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Run the solver and print the result
result = solve_scheduling()
print(result)