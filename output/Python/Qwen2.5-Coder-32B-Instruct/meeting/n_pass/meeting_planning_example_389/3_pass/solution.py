import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Bayview"): 26,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Bayview"): 15,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Mission District"): 13
}

# Define the meeting constraints
meetings = {
    "Sarah": {"location": "Fisherman's Wharf", "start": "14:45", "end": "17:30", "min_duration": 105},
    "Mary": {"location": "Richmond District", "start": "13:00", "end": "19:15", "min_duration": 75},
    "Helen": {"location": "Mission District", "start": "21:45", "end": "22:30", "min_duration": 30},
    "Thomas": {"location": "Bayview", "start": "15:15", "end": "18:45", "min_duration": 120}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_schedule():
    current_location = "Haight-Ashbury"
    current_time = parse_time("9:00")
    itinerary = []

    def can_meet(meeting, start_time):
        meeting_start = parse_time(meeting["start"])
        meeting_end = parse_time(meeting["end"])
        return start_time >= meeting_start and start_time + timedelta(minutes=meeting["min_duration"]) <= meeting_end

    def travel_to(location):
        nonlocal current_time, current_location
        travel_time = travel_times[(current_location, location)]
        current_time += timedelta(minutes=travel_time)
        current_location = location

    # Sort meetings by earliest possible start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]))

    for person, meeting in sorted_meetings:
        # Calculate the earliest possible start time considering travel time
        earliest_possible_start = max(current_time + timedelta(minutes=travel_times.get((current_location, meeting["location"]), 0)), parse_time(meeting["start"]))
        
        # Calculate the meeting end time based on the earliest possible start time
        meeting_start = earliest_possible_start
        meeting_end = meeting_start + timedelta(minutes=meeting["min_duration"])

        # Adjust meeting start time if it exceeds the person's available end time
        if meeting_end > parse_time(meeting["end"]):
            meeting_start = parse_time(meeting["end"]) - timedelta(minutes=meeting["min_duration"])
            meeting_end = meeting_start + timedelta(minutes=meeting["min_duration"])

        if can_meet(meeting, meeting_start):
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": person,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_time = meeting_end

    return {"itinerary": itinerary}

# Generate the optimal meeting schedule
schedule = find_meeting_schedule()

# Output the result as a JSON-formatted dictionary
print(json.dumps(schedule, indent=4))