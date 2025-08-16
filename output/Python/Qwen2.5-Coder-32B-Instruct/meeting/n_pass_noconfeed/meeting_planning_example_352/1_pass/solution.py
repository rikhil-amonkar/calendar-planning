import json
from datetime import datetime, timedelta

# Define travel times
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

# Define meeting constraints
meetings = {
    "Karen": {"location": "Nob Hill", "start": "21:15", "end": "21:45", "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": "12:30", "end": "19:45", "min_duration": 90},
    "Sandra": {"location": "Chinatown", "start": "7:15", "end": "19:15", "min_duration": 75},
    "Nancy": {"location": "Marina District", "start": "11:00", "end": "20:15", "min_duration": 105},
}

# Convert time strings to datetime objects
def time_to_dt(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Calculate the latest start time for a meeting to meet the minimum duration requirement
def calculate_latest_start(meeting):
    end_time = time_to_dt(meeting["end"])
    min_duration = timedelta(minutes=meeting["min_duration"])
    return end_time - min_duration

# Check if a meeting can be scheduled given the current time and location
def can_meet(current_time, current_location, meeting):
    meeting_start = time_to_dt(meeting["start"])
    meeting_end = time_to_dt(meeting["end"])
    travel_time = travel_times[(current_location, meeting["location"])]
    earliest_arrival = current_time + timedelta(minutes=travel_time)
    latest_start = calculate_latest_start(meeting)
    return earliest_arrival <= latest_start and earliest_arrival < meeting_end

# Find the next possible meeting
def find_next_meeting(current_time, current_location, remaining_meetings):
    for person, meeting in remaining_meetings.items():
        if can_meet(current_time, current_location, meeting):
            return person, meeting
    return None, None

# Schedule meetings
def schedule_meetings(start_time, start_location):
    current_time = start_time
    current_location = start_location
    remaining_meetings = meetings.copy()
    itinerary = []

    while remaining_meetings:
        person, meeting = find_next_meeting(current_time, current_location, remaining_meetings)
        if not person:
            break

        travel_time = travel_times[(current_location, meeting["location"])]
        meeting_start = current_time + timedelta(minutes=travel_time)
        meeting_end = meeting_start + timedelta(minutes=meeting["min_duration"])

        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": person,
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M")
        })

        current_time = meeting_end
        current_location = meeting["location"]
        del remaining_meetings[person]

    return itinerary

# Main function
def main():
    start_time = time_to_dt("9:00")
    start_location = "Union Square"
    itinerary = schedule_meetings(start_time, start_location)
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()