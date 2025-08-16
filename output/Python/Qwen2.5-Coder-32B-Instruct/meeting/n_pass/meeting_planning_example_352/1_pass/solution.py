import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Marina District"): 18,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Marina District"): 11,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Chinatown"): 16,
}

# Define the meeting constraints
meetings = {
    "Karen": {"location": "Nob Hill", "start": "21:15", "end": "21:45", "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": "12:30", "end": "19:45", "min_duration": 90},
    "Sandra": {"location": "Chinatown", "start": "7:15", "end": "19:15", "min_duration": 75},
    "Nancy": {"location": "Marina District", "start": "11:00", "end": "20:15", "min_duration": 105},
}

# Convert time strings to datetime objects for easier manipulation
def time_to_datetime(time_str, base_date):
    return datetime.strptime(f"{base_date} {time_str}", "%Y-%m-%d %H:%M")

# Calculate the latest possible start time for a meeting
def latest_start(meeting, base_date):
    end_time = time_to_datetime(meeting["end"], base_date)
    return end_time - timedelta(minutes=meeting["min_duration"])

# Calculate the earliest possible end time for a meeting
def earliest_end(meeting, base_date):
    start_time = time_to_datetime(meeting["start"], base_date)
    return start_time + timedelta(minutes=meeting["min_duration"])

# Check if two meetings overlap in time and location
def meetings_overlap(meeting1, meeting2, base_date):
    start1 = time_to_datetime(meeting1["start"], base_date)
    end1 = time_to_datetime(meeting1["end"], base_date)
    start2 = time_to_datetime(meeting2["start"], base_date)
    end2 = time_to_datetime(meeting2["end"], base_date)
    return meeting1["location"] == meeting2["location"] and not (end1 <= start2 or end2 <= start1)

# Find the optimal schedule
def find_optimal_schedule(base_date):
    schedule = []
    current_location = "Union Square"
    current_time = time_to_datetime("9:00", base_date)

    # Sort meetings by their latest possible start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: latest_start(x[1], base_date))

    for person, meeting in sorted_meetings:
        latest_start_time = latest_start(meeting, base_date)
        earliest_end_time = earliest_end(meeting, base_date)

        # Find the earliest possible time to start the meeting after traveling
        travel_time = travel_times.get((current_location, meeting["location"]), float('inf'))
        earliest_possible_start = current_time + timedelta(minutes=travel_time)

        # Adjust the start time to the latest possible start time if necessary
        start_time = max(earliest_possible_start, latest_start_time)

        # Check if the meeting can fit within the remaining time
        if start_time < earliest_end_time:
            end_time = start_time + timedelta(minutes=meeting["min_duration"])
            schedule.append({
                "action": "meet",
                "location": meeting["location"],
                "person": person,
                "start_time": start_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M")
            })
            current_location = meeting["location"]
            current_time = end_time

    return schedule

# Base date for time calculations
base_date = "2023-10-01"

# Find and print the optimal schedule
optimal_schedule = find_optimal_schedule(base_date)
print(json.dumps({"itinerary": optimal_schedule}))