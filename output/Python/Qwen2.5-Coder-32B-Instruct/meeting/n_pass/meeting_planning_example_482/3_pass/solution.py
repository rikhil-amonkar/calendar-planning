import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define meeting constraints
meetings = {
    "Stephanie": {"location": "Mission District", "start": "8:15", "end": "13:45", "min_duration": 90},
    "Sandra": {"location": "Bayview", "start": "13:00", "end": "19:30", "min_duration": 15},
    "Richard": {"location": "Pacific Heights", "start": "7:15", "end": "10:15", "min_duration": 75},
    "Brian": {"location": "Russian Hill", "start": "12:15", "end": "16:00", "min_duration": 120},
    "Jason": {"location": "Fisherman's Wharf", "start": "8:30", "end": "17:45", "min_duration": 60},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

# Convert time object to datetime object for calculations
def to_datetime(time_obj):
    return datetime.combine(datetime.today(), time_obj)

# Calculate the latest start time for a meeting
def latest_start(meeting):
    end_time = parse_time(meeting["end"])
    return (to_datetime(end_time) - timedelta(minutes=meeting["min_duration"])).time()

# Calculate the earliest end time for a meeting
def earliest_end(meeting):
    start_time = parse_time(meeting["start"])
    return (to_datetime(start_time) + timedelta(minutes=meeting["min_duration"])).time()

# Check if two time intervals overlap
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Main function to find the optimal schedule
def find_optimal_schedule():
    current_location = "Haight-Ashbury"
    current_time = parse_time("9:00")
    itinerary = []

    # Sort meetings by their start times
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]))

    for name, meeting in sorted_meetings:
        location = meeting["location"]
        meeting_start = parse_time(meeting["start"])
        meeting_end = parse_time(meeting["end"])
        min_duration = meeting["min_duration"]

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]

        # Calculate the earliest possible start time for the meeting
        earliest_meeting_start = max(
            (to_datetime(current_time) + timedelta(minutes=travel_time)).time(),
            meeting_start
        )

        # Calculate the latest possible end time for the meeting
        latest_meeting_end = min(
            (to_datetime(earliest_meeting_start) + timedelta(minutes=min_duration)).time(),
            meeting_end
        )

        # If the meeting can fit within the available time
        if earliest_meeting_start <= latest_meeting_end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": earliest_meeting_start.strftime("%H:%M"),
                "end_time": latest_meeting_end.strftime("%H:%M")
            })
            current_location = location
            current_time = latest_meeting_end

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule()

# Output the result as a JSON-formatted dictionary
output = {
    "itinerary": optimal_itinerary
}

print(json.dumps(output))