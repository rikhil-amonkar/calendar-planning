import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Haight-Ashbury"): 17,
}

# Define meetings constraints
meetings = {
    "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "duration": 30},
    "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "duration": 30},
    "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "duration": 60},
    "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "duration": 120},
    "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "duration": 105},
    "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "duration": 75},
    "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "duration": 105},
    "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "duration": 45},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def get_travel_time(start_loc, end_loc):
    if (start_loc, end_loc) in travel_times:
        return travel_times[(start_loc, end_loc)]
    elif (end_loc, start_loc) in travel_times:
        return travel_times[(end_loc, start_loc)]
    else:
        return float('inf')

def find_meeting_times(schedule, current_time, current_location):
    available_meetings = []
    for person, details in meetings.items():
        if person not in schedule:
            start_time = parse_time(details["start"])
            end_time = parse_time(details["end"])
            if current_time + timedelta(minutes=details["duration"]) <= end_time:
                available_meetings.append((person, start_time, end_time))
    return available_meetings

def schedule_meetings(current_time, current_location, schedule):
    if len(schedule) == len(meetings):
        return schedule

    available_meetings = find_meeting_times(schedule, current_time, current_location)
    available_meetings.sort(key=lambda x: x[1])  # Sort by earliest start time

    best_schedule = None
    for person, start_time, end_time in available_meetings:
        travel_time = get_travel_time(current_location, meetings[person]["location"])
        arrival_time = current_time + timedelta(minutes=travel_time)

        if arrival_time < start_time:
            meeting_start = start_time
        else:
            meeting_start = arrival_time

        meeting_end = meeting_start + timedelta(minutes=meetings[person]["duration"])

        if meeting_end <= end_time:
            new_schedule = schedule.copy()
            new_schedule[person] = {
                "location": meetings[person]["location"],
                "start": format_time(meeting_start),
                "end": format_time(meeting_end)
            }
            result = schedule_meetings(meeting_end, meetings[person]["location"], new_schedule)
            if result:
                if best_schedule is None or len(result) > len(best_schedule):
                    best_schedule = result

    return best_schedule

start_time = parse_time("9:00")
initial_location = "Marina District"
schedule = schedule_meetings(start_time, initial_location, {})

itinerary = []
for person, details in sorted(schedule.items(), key=lambda x: parse_time(x[1]["start"])):
    itinerary.append({
        "action": "meet",
        "location": details["location"],
        "person": person,
        "start_time": details["start"],
        "end_time": details["end"]
    })

output = {"itinerary": itinerary}
print(json.dumps(output))