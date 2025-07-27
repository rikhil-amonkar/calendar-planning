from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their details
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

    # Current location is Haight-Ashbury at 9:00 AM
    current_location = "Haight-Ashbury"
    current_time = 9 * 60  # in minutes since midnight

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    for friend in friends:
        friend["start_avail_min"] = time_to_minutes(friend["start_avail"])
        friend["end_avail_min"] = time_to_minutes(friend["end_avail"])

    # Define travel times (simplified for this example; in practice, use a dictionary or matrix)
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
        ("Mission District", "Haight-Ashbury"): 11,
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
        ("Marina District", "Sunset District"): 19,
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

    # Define variables for each meeting's start and end times
    meetings = []
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "start_avail_min": friend["start_avail_min"],
            "end_avail_min": friend["end_avail_min"],
            "min_duration": friend["min_duration"]
        })

    # Add constraints for each meeting
    for meeting in meetings:
        s.add(meeting["start"] >= meeting["start_avail_min"])
        s.add(meeting["end"] <= meeting["end_avail_min"])
        s.add(meeting["end"] - meeting["start"] >= meeting["min_duration"])

    # Define the order of meetings to account for travel times
    # We'll use a list to represent the sequence of meetings
    sequence = [Int(f'seq_{i}') for i in range(len(meetings))]
    s.add(Distinct(sequence))
    for i in range(len(sequence)):
        s.add(sequence[i] >= 0)
        s.add(sequence[i] < len(meetings))

    # Add constraints for travel times between consecutive meetings
    for i in range(len(sequence) - 1):
        current_meeting = meetings[m.evaluate(sequence[i]).as_long() if s.check() == sat else 0]
        next_meeting = meetings[m.evaluate(sequence[i + 1]).as_long() if s.check() == sat else 0]
        travel_time = travel_times.get((current_meeting["location"], next_meeting["location"]), 0)
        s.add(next_meeting["start"] >= current_meeting["end"] + travel_time)

    # Ensure the first meeting starts after the current time (9:00 AM)
    first_meeting = meetings[m.evaluate(sequence[0]).as_long() if s.check() == sat else 0]
    s.add(first_meeting["start"] >= current_time)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Sort meetings by their sequence
        seq_order = sorted([(m.evaluate(seq).as_long(), idx] for idx, seq in enumerate(sequence))
        for seq, idx in seq_order:
            meeting = meetings[idx]
            start_val = m.evaluate(meeting["start"]).as_long()
            end_val = m.evaluate(meeting["end"]).as_long()
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": start_time,
                "end_time": end_time
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))