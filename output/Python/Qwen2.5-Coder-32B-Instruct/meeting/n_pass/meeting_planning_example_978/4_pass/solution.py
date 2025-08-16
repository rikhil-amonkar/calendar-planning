import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "The Castro"): 20,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "The Castro"): 22,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "The Castro"): 16,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Nob Hill"): 13,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "The Castro"): 21,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Nob Hill"): 16,
}

# Define meeting constraints
meetings = {
    "Stephanie": {"location": "Fisherman's Wharf", "start": "15:30", "end": "22:00", "min_duration": 30},
    "Lisa": {"location": "Financial District", "start": "10:45", "end": "17:15", "min_duration": 15},
    "Melissa": {"location": "Russian Hill", "start": "17:00", "end": "21:45", "min_duration": 120},
    "Betty": {"location": "Marina District", "start": "10:45", "end": "14:15", "min_duration": 60},
    "Sarah": {"location": "Richmond District", "start": "16:15", "end": "19:30", "min_duration": 105},
    "Daniel": {"location": "Pacific Heights", "start": "18:30", "end": "21:45", "min_duration": 60},
    "Joshua": {"location": "Haight-Ashbury", "start": "09:00", "end": "15:30", "min_duration": 15},
    "Joseph": {"location": "Presidio", "start": "07:00", "end": "13:00", "min_duration": 45},
    "Andrew": {"location": "Nob Hill", "start": "19:45", "end": "22:00", "min_duration": 105},
    "John": {"location": "The Castro", "start": "13:15", "end": "19:45", "min_duration": 45},
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