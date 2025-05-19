import json
from datetime import datetime, timedelta
from itertools import permutations

# Travel distances in minutes
travel_times = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# Meeting constraints
constraints = {
    "David": {"location": "Mission District", "start": "08:00", "end": "19:45", "duration": 45},
    "Kenneth": {"location": "Alamo Square", "start": "14:00", "end": "19:45", "duration": 120},
    "John": {"location": "Pacific Heights", "start": "17:00", "end": "20:00", "duration": 15},
    "Charles": {"location": "Union Square", "start": "21:45", "end": "22:45", "duration": 60},
    "Deborah": {"location": "Golden Gate Park", "start": "07:00", "end": "18:15", "duration": 90},
    "Karen": {"location": "Sunset District", "start": "17:45", "end": "21:15", "duration": 15},
    "Carol": {"location": "Presidio", "start": "08:15", "end": "09:15", "duration": 30},
}

arrival_time = datetime.strptime('09:00', '%H:%M')

# Function to convert time string to minutes since midnight
def to_minutes(time_str):
    time = datetime.strptime(time_str, '%H:%M')
    return time.hour * 60 + time.minute

# Function to check if a meeting can be scheduled
def can_schedule(meeting_start, meeting_end, travel_time):
    return (meeting_start + travel_time <= to_minutes(constraints[meeting_person]["end"])
            and meeting_end >= to_minutes(constraints[meeting_person]["start"]))

# Function to get meeting schedule
def get_meeting_schedule():
    best_schedule = []
    best_schedule_length = 0
    possible_meetings = {}

    # Create a list of all possible meetings
    for person, info in constraints.items():
        possible_meetings[person] = (info["location"], info["duration"], to_minutes(info["start"]), to_minutes(info["end"]))

    # Check all permutations of meetings to find a valid schedule
    for order in permutations(possible_meetings.keys()):
        current_time = to_minutes('09:00')  # Start time
        current_schedule = []
        
        for person in order:
            location, duration, start_time, end_time = possible_meetings[person]
            meeting_start = max(start_time, current_time)  # When we can actually start the meeting
            meeting_end = meeting_start + duration

            if meeting_end <= end_time and can_schedule(meeting_start, meeting_end, travel_times.get((current_item['location'], location), 0)):
                travel_time = travel_times.get(('Chinatown', location), 0)
                current_time = meeting_end + travel_time
                current_schedule.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": f"{meeting_start // 60}:{meeting_start % 60:02}",
                    "end_time": f"{meeting_end // 60}:{meeting_end % 60:02}"
                })

        if len(current_schedule) > best_schedule_length:
            best_schedule_length = len(current_schedule)
            best_schedule = current_schedule

    return best_schedule

# Constructing the final output
final_schedule = get_meeting_schedule()
itinerary = {"itinerary": final_schedule}

# Output the final schedule as JSON
print(json.dumps(itinerary, indent=2))