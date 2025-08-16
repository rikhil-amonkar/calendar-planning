import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    # ... [same as before]
    ("Fisherman's Wharf", "Russian Hill"): 7,
    # ... [other travel times remain unchanged]
}

# Define meeting constraints
meetings = {
    "Stephanie": {"location": "Fisherman's Wharf", "start": "15:30", "end": "22:00", "min_duration": 30},
    # ... [other meeting constraints remain unchanged]
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_schedule():
    current_time = parse_time("09:00")
    current_location = "Embarcadero"
    itinerary = []

    def can_meet(person, start, end, duration):
        person_start = parse_time(meetings[person]["start"])
        person_end = parse_time(meetings[person]["end"])
        available_start = max(start, person_start)
        available_end = min(end, person_end)
        return (available_end - available_start).total_seconds() / 60 >= duration

    def meet(person, start, end):
        person_start = parse_time(meetings[person]["start"])
        person_end = parse_time(meetings[person]["end"])
        available_start = max(start, person_start)
        available_end = min(end, person_end)
        meeting_duration = meetings[person]["min_duration"]
        meeting_start = available_start
        meeting_end = meeting_start + timedelta(minutes=meeting_duration)
        if meeting_end > available_end:
            meeting_start = available_end - timedelta(minutes=meeting_duration)
            meeting_end = available_end
        return meeting_start, meeting_end

    while current_time < parse_time("22:00"):
        next_meeting = None
        for person, details in meetings.items():
            location = details["location"]
            min_duration = details["min_duration"]
            if can_meet(person, current_time, parse_time("22:00"), min_duration):
                if current_location == location:
                    travel_time = 0
                else:
                    travel_time = travel_times.get((current_location, location))
                    if travel_time is None:
                        raise ValueError(f"No travel time defined from {current_location} to {location}")
                arrival_time = current_time + timedelta(minutes=travel_time)
                if can_meet(person, arrival_time, parse_time("22:00"), min_duration):
                    meeting_start, meeting_end = meet(person, arrival_time, parse_time("22:00"))
                    if next_meeting is None or (meeting_end - meeting_start) > (next_meeting[1] - next_meeting[0]):
                        next_meeting = (arrival_time, meeting_end, location, person)

        if next_meeting:
            arrival_time, meeting_end, location, person = next_meeting
            if current_location != location:
                itinerary.append({
                    "action": "travel",
                    "location": location,
                    "person": None,
                    "start_time": time_to_str(current_time),
                    "end_time": time_to_str(arrival_time)
                })
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": time_to_str(arrival_time),
                "end_time": time_to_str(meeting_end)
            })
            current_time = meeting_end
            current_location = location
        else:
            break

    return itinerary

try:
    itinerary = find_meeting_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
except ValueError as e:
    print(f"Error: {e}")