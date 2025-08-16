import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# Define meeting constraints
meetings = {
    'Jessica': {'location': 'Embarcadero', 'start': '16:45', 'end': '19:00', 'min_duration': 30},
    'Sandra': {'location': 'Richmond District', 'start': '18:30', 'end': '21:45', 'min_duration': 120},
    'Jason': {'location': 'Fisherman\'s Wharf', 'start': '16:00', 'end': '16:45', 'min_duration': 30},
}

# Convert time strings to datetime objects for easier manipulation
def time_to_dt(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the end time of a meeting
def calculate_meeting_end(start_time, min_duration):
    return start_time + timedelta(minutes=min_duration)

# Check if a meeting can fit within the person's availability
def can_fit_meeting(meeting_start, meeting_end, person_start, person_end):
    return meeting_start >= person_start and meeting_end <= person_end

# Find the optimal meeting schedule
def find_optimal_schedule():
    current_location = 'Bayview'
    current_time = time_to_dt('9:00')
    itinerary = []

    # Try to meet Jason first since his window is the earliest
    jason_start = time_to_dt(meetings['Jason']['start'])
    jason_end = time_to_dt(meetings['Jason']['end'])
    jason_duration = meetings['Jason']['min_duration']
    jason_location = meetings['Jason']['location']

    travel_to_jason = travel_times[(current_location, jason_location)]
    jason_meeting_start = jason_start
    jason_meeting_end = calculate_meeting_end(jason_meeting_start, jason_duration)

    if current_time + timedelta(minutes=travel_to_jason) <= jason_meeting_start:
        current_time += timedelta(minutes=travel_to_jason)
        if can_fit_meeting(jason_meeting_start, jason_meeting_end, jason_start, jason_end):
            itinerary.append({
                "action": "meet",
                "location": jason_location,
                "person": "Jason",
                "start_time": jason_meeting_start.strftime('%H:%M'),
                "end_time": jason_meeting_end.strftime('%H:%M')
            })
            current_time = jason_meeting_end
            current_location = jason_location

    # Try to meet Jessica next
    jessica_start = time_to_dt(meetings['Jessica']['start'])
    jessica_end = time_to_dt(meetings['Jessica']['end'])
    jessica_duration = meetings['Jessica']['min_duration']
    jessica_location = meetings['Jessica']['location']

    travel_to_jessica = travel_times[(current_location, jessica_location)]
    jessica_meeting_start = jessica_start
    jessica_meeting_end = calculate_meeting_end(jessica_meeting_start, jessica_duration)

    if current_time + timedelta(minutes=travel_to_jessica) <= jessica_meeting_start:
        current_time += timedelta(minutes=travel_to_jessica)
        if can_fit_meeting(jessica_meeting_start, jessica_meeting_end, jessica_start, jessica_end):
            itinerary.append({
                "action": "meet",
                "location": jessica_location,
                "person": "Jessica",
                "start_time": jessica_meeting_start.strftime('%H:%M'),
                "end_time": jessica_meeting_end.strftime('%H:%M')
            })
            current_time = jessica_meeting_end
            current_location = jessica_location

    # Finally, try to meet Sandra
    sandra_start = time_to_dt(meetings['Sandra']['start'])
    sandra_end = time_to_dt(meetings['Sandra']['end'])
    sandra_duration = meetings['Sandra']['min_duration']
    sandra_location = meetings['Sandra']['location']

    travel_to_sandra = travel_times[(current_location, sandra_location)]
    sandra_meeting_start = sandra_start
    sandra_meeting_end = calculate_meeting_end(sandra_meeting_start, sandra_duration)

    if current_time + timedelta(minutes=travel_to_sandra) <= sandra_meeting_start:
        current_time += timedelta(minutes=travel_to_sandra)
        if can_fit_meeting(sandra_meeting_start, sandra_meeting_end, sandra_start, sandra_end):
            itinerary.append({
                "action": "meet",
                "location": sandra_location,
                "person": "Sandra",
                "start_time": sandra_meeting_start.strftime('%H:%M'),
                "end_time": sandra_meeting_end.strftime('%H:%M')
            })

    return itinerary

# Generate the solution
solution = {"itinerary": find_optimal_schedule()}
print(json.dumps(solution))