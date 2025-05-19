import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Nob Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Nob Hill'): 8,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Nob Hill'): 9,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Nob Hill'): 12,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
}

# Define meeting times and constraints
meetings = {
    "James": {"location": "Pacific Heights", "start": "20:00", "end": "22:00", "min_duration": 120},
    "Robert": {"location": "Chinatown", "start": "12:15", "end": "16:45", "min_duration": 90},
    "Jeffrey": {"location": "Union Square", "start": "09:30", "end": "15:30", "min_duration": 120},
    "Carol": {"location": "Mission District", "start": "18:15", "end": "21:15", "min_duration": 15},
    "Mark": {"location": "Golden Gate Park", "start": "11:30", "end": "17:45", "min_duration": 15},
    "Sandra": {"location": "Nob Hill", "start": "08:00", "end": "15:30", "min_duration": 15},
}

# Define arrival time
arrival_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Function to add a meeting to the itinerary
def schedule_meeting(person, location, start_time, end_time):
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M"),
    })

# Helper function to calculate available time slots
def available_time_slots(person):
    constraints = meetings[person]
    start = datetime.strptime(constraints['start'], "%H:%M")
    end = datetime.strptime(constraints['end'], "%H:%M")
    duration = timedelta(minutes=constraints['min_duration'])
    return (start, end, duration)

# Schedule meetings based on constraints and travel times
current_time = arrival_time
# Meet Sandra first
if current_time < datetime.strptime(meetings["Sandra"]["start"], "%H:%M"):
    current_time = datetime.strptime(meetings["Sandra"]["start"], "%H:%M")
schedule_meeting("Sandra", "Nob Hill", current_time, current_time + timedelta(minutes=15))
current_time += timedelta(minutes=15)

# Meet Jeffrey next
jeffrey_start, jeffrey_end, jeffrey_duration = available_time_slots("Jeffrey")
jeffrey_meeting_start = max(current_time, jeffrey_start)  # After current time
jeffrey_meeting_end = jeffrey_meeting_start + jeffrey_duration
if jeffrey_meeting_end <= jeffrey_end:
    schedule_meeting("Jeffrey", "Union Square", jeffrey_meeting_start, jeffrey_meeting_end)
    current_time = jeffrey_meeting_end

# Meet Robert next
robert_start, robert_end, robert_duration = available_time_slots("Robert")
robert_meeting_start = max(current_time, robert_start)  # After current time
robert_meeting_end = robert_meeting_start + robert_duration
if robert_meeting_end <= robert_end:
    travel_time = travel_times[("Union Square", "Chinatown")]
    robert_meeting_start += timedelta(minutes=travel_time)
    robert_meeting_end += timedelta(minutes=travel_time)
    schedule_meeting("Robert", "Chinatown", robert_meeting_start, robert_meeting_end)
    current_time = robert_meeting_end

# Meet Mark next
mark_start, mark_end, mark_duration = available_time_slots("Mark")
mark_meeting_start = max(current_time, mark_start)  # After current time
mark_meeting_end = mark_meeting_start + mark_duration
if mark_meeting_end <= mark_end:
    travel_time = travel_times[("Chinatown", "Golden Gate Park")]
    mark_meeting_start += timedelta(minutes=travel_time)
    mark_meeting_end += timedelta(minutes=travel_time)
    schedule_meeting("Mark", "Golden Gate Park", mark_meeting_start, mark_meeting_end)
    current_time = mark_meeting_end

# Meet James last
james_start, james_end, james_duration = available_time_slots("James")
james_meeting_start = max(current_time, james_start)  # After current time
james_meeting_end = james_meeting_start + james_duration
if james_meeting_end <= james_end:
    travel_time = travel_times[("Golden Gate Park", "Pacific Heights")]
    james_meeting_start += timedelta(minutes=travel_time)
    james_meeting_end += timedelta(minutes=travel_time)
    schedule_meeting("James", "Pacific Heights", james_meeting_start, james_meeting_end)

# Meet Carol before finishing
carol_start, carol_end, carol_duration = available_time_slots("Carol")
carol_meeting_start = max(current_time, carol_start)  # After current time
carol_meeting_end = carol_meeting_start + carol_duration
if carol_meeting_end <= carol_end:
    travel_time = travel_times[("Pacific Heights", "Mission District")]
    carol_meeting_start += timedelta(minutes=travel_time)
    carol_meeting_end += timedelta(minutes=travel_time)
    schedule_meeting("Carol", "Mission District", carol_meeting_start, carol_meeting_end)

# Output the final itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=2))