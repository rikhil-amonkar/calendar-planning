import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22,
}

# Define meeting constraints
constraints = {
    "Karen": {"location": "Russian Hill", "start": "20:45", "end": "21:45", "min_duration": 60},
    "Jessica": {"location": "The Castro", "start": "15:45", "end": "19:30", "min_duration": 60},
    "Matthew": {"location": "Richmond District", "start": "07:30", "end": "15:15", "min_duration": 15},
    "Michelle": {"location": "Marina District", "start": "10:30", "end": "18:45", "min_duration": 75},
    "Carol": {"location": "North Beach", "start": "12:00", "end": "17:00", "min_duration": 90},
    "Stephanie": {"location": "Union Square", "start": "10:45", "end": "14:15", "min_duration": 30},
    "Linda": {"location": "Golden Gate Park", "start": "10:45", "end": "22:00", "min_duration": 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    start_time = parse_time("9:00")
    current_location = "Sunset District"
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))

    for name, constraint in sorted_constraints:
        location = constraint["location"]
        start = parse_time(constraint["start"])
        end = parse_time(constraint["end"])
        min_duration = constraint["min_duration"]

        # Calculate travel time to the next location
        travel_time = travel_times.get((current_location, location), float('inf'))

        # Check if we can reach the location on time
        arrival_time = start_time + timedelta(minutes=travel_time)

        if arrival_time <= start:
            # We can meet the person
            meeting_start = max(arrival_time, start)
            meeting_end = meeting_start + timedelta(minutes=min_duration)

            # Ensure the meeting does not exceed the person's availability
            if meeting_end <= end:
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": name,
                    "start_time": time_to_str(meeting_start),
                    "end_time": time_to_str(meeting_end)
                })
                start_time = meeting_end
                current_location = location
            else:
                # Try to adjust the meeting time to fit within the person's availability
                adjusted_start = end - timedelta(minutes=min_duration)
                if adjusted_start >= arrival_time:
                    itinerary.append({
                        "action": "meet",
                        "location": location,
                        "person": name,
                        "start_time": time_to_str(adjusted_start),
                        "end_time": time_to_str(end)
                    })
                    start_time = end
                    current_location = location
        else:
            # If we cannot reach the location on time, skip this meeting
            continue

    return itinerary

optimal_schedule = find_optimal_schedule()
result = {"itinerary": optimal_schedule}
print(json.dumps(result))