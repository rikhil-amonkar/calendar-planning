import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17,
}

# Define meeting constraints
meetings = {
    "William": {"location": "Russian Hill", "start": "18:30", "end": "20:45", "min_duration": 105},
    "Michelle": {"location": "Chinatown", "start": "8:15", "end": "14:00", "min_duration": 15},
    "George": {"location": "Presidio", "start": "10:30", "end": "18:45", "min_duration": 30},
    "Robert": {"location": "Fisherman's Wharf", "start": "9:00", "end": "13:45", "min_duration": 30},
}

# Convert times to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Calculate the latest possible start time for a meeting
def latest_start(meeting, duration):
    end_time = parse_time(meeting["end"])
    return end_time - timedelta(minutes=duration)

# Calculate the earliest possible end time for a meeting
def earliest_end(meeting, duration):
    start_time = parse_time(meeting["start"])
    return start_time + timedelta(minutes=duration)

# Check if two time intervals overlap
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Main function to find the optimal schedule
def find_optimal_schedule():
    current_location = "Sunset District"
    current_time = parse_time("9:00")
    itinerary = []

    # Sort meetings by their start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]))

    for person, meeting in sorted_meetings:
        location = meeting["location"]
        min_duration = meeting["min_duration"]
        start_time = parse_time(meeting["start"])
        end_time = parse_time(meeting["end"])

        # Calculate the latest possible start and earliest possible end for this meeting
        latest_start_time = latest_start(meeting, min_duration)
        earliest_end_time = earliest_end(meeting, min_duration)

        # Find the earliest possible time to travel to the meeting location
        travel_time = travel_times[(current_location, location)]
        potential_start_time = current_time + timedelta(minutes=travel_time)

        # Adjust the start time to fit within the meeting window
        actual_start_time = max(potential_start_time, start_time)
        actual_end_time = actual_start_time + timedelta(minutes=min_duration)

        # Ensure the meeting does not overlap with other meetings
        valid_meeting = True
        for existing_meeting in itinerary:
            if intervals_overlap(actual_start_time, actual_end_time, parse_time(existing_meeting["start_time"]), parse_time(existing_meeting["end_time"])):
                valid_meeting = False
                break

        if valid_meeting and actual_end_time <= end_time:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": actual_start_time.strftime("%H:%M"),
                "end_time": actual_end_time.strftime("%H:%M")
            })
            current_location = location
            current_time = actual_end_time

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule()

# Output the result as JSON
result = {"itinerary": optimal_itinerary}
print(json.dumps(result))