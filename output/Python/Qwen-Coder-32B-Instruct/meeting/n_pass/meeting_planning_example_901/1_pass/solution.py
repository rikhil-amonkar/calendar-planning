import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    'Russian Hill': {'Russian Hill': 0, 'Pacific Heights': 7, 'North Beach': 5, 'Golden Gate Park': 21, 'Embarcadero': 8, 'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'Mission District': 16, 'Alamo Square': 15, 'Bayview': 23, 'Richmond District': 14},
    'Pacific Heights': {'Russian Hill': 7, 'Pacific Heights': 0, 'North Beach': 9, 'Golden Gate Park': 15, 'Embarcadero': 10, 'Haight-Ashbury': 11, 'Fisherman\'s Wharf': 13, 'Mission District': 15, 'Alamo Square': 10, 'Bayview': 22, 'Richmond District': 12},
    'North Beach': {'Russian Hill': 5, 'Pacific Heights': 9, 'North Beach': 0, 'Golden Gate Park': 22, 'Embarcadero': 6, 'Haight-Ashbury': 18, 'Fisherman\'s Wharf': 5, 'Mission District': 18, 'Alamo Square': 16, 'Bayview': 25, 'Richmond District': 18},
    'Golden Gate Park': {'Russian Hill': 21, 'Pacific Heights': 15, 'North Beach': 22, 'Golden Gate Park': 0, 'Embarcadero': 25, 'Haight-Ashbury': 7, 'Fisherman\'s Wharf': 24, 'Mission District': 17, 'Alamo Square': 9, 'Bayview': 23, 'Richmond District': 7},
    'Embarcadero': {'Russian Hill': 8, 'Pacific Heights': 10, 'North Beach': 6, 'Golden Gate Park': 25, 'Embarcadero': 0, 'Haight-Ashbury': 20, 'Fisherman\'s Wharf': 6, 'Mission District': 19, 'Alamo Square': 16, 'Bayview': 21, 'Richmond District': 21},
    'Haight-Ashbury': {'Russian Hill': 17, 'Pacific Heights': 11, 'North Beach': 18, 'Golden Gate Park': 7, 'Embarcadero': 20, 'Haight-Ashbury': 0, 'Fisherman\'s Wharf': 22, 'Mission District': 11, 'Alamo Square': 5, 'Bayview': 18, 'Richmond District': 10},
    'Fisherman\'s Wharf': {'Russian Hill': 7, 'Pacific Heights': 12, 'North Beach': 6, 'Golden Gate Park': 25, 'Embarcadero': 6, 'Haight-Ashbury': 22, 'Fisherman\'s Wharf': 0, 'Mission District': 22, 'Alamo Square': 19, 'Bayview': 26, 'Richmond District': 18},
    'Mission District': {'Russian Hill': 16, 'Pacific Heights': 15, 'North Beach': 17, 'Golden Gate Park': 17, 'Embarcadero': 19, 'Haight-Ashbury': 11, 'Fisherman\'s Wharf': 22, 'Mission District': 0, 'Alamo Square': 10, 'Bayview': 14, 'Richmond District': 20},
    'Alamo Square': {'Russian Hill': 15, 'Pacific Heights': 10, 'North Beach': 15, 'Golden Gate Park': 9, 'Embarcadero': 16, 'Haight-Ashbury': 5, 'Fisherman\'s Wharf': 19, 'Mission District': 10, 'Alamo Square': 0, 'Bayview': 16, 'Richmond District': 11},
    'Bayview': {'Russian Hill': 23, 'Pacific Heights': 22, 'North Beach': 22, 'Golden Gate Park': 22, 'Embarcadero': 19, 'Haight-Ashbury': 18, 'Fisherman\'s Wharf': 25, 'Mission District': 13, 'Alamo Square': 16, 'Bayview': 0, 'Richmond District': 25},
    'Richmond District': {'Russian Hill': 14, 'Pacific Heights': 12, 'North Beach': 17, 'Golden Gate Park': 7, 'Embarcadero': 19, 'Haight-Ashbury': 10, 'Fisherman\'s Wharf': 18, 'Mission District': 20, 'Alamo Square': 11, 'Bayview': 25, 'Richmond District': 0}
}

# Define the meeting constraints
meetings = {
    'Emily': {'location': 'Pacific Heights', 'start': '9:15', 'end': '13:45', 'min_duration': 120},
    'Helen': {'location': 'North Beach', 'start': '13:45', 'end': '18:45', 'min_duration': 30},
    'Kimberly': {'location': 'Golden Gate Park', 'start': '18:45', 'end': '21:15', 'min_duration': 75},
    'James': {'location': 'Embarcadero', 'start': '10:30', 'end': '11:30', 'min_duration': 30},
    'Linda': {'location': 'Haight-Ashbury', 'start': '7:30', 'end': '19:15', 'min_duration': 15},
    'Paul': {'location': 'Fisherman\'s Wharf', 'start': '14:45', 'end': '18:45', 'min_duration': 90},
    'Anthony': {'location': 'Mission District', 'start': '8:00', 'end': '14:45', 'min_duration': 105},
    'Nancy': {'location': 'Alamo Square', 'start': '8:30', 'end': '13:45', 'min_duration': 120},
    'William': {'location': 'Bayview', 'start': '17:30', 'end': '20:30', 'min_duration': 120},
    'Margaret': {'location': 'Richmond District', 'start': '15:15', 'end': '18:15', 'min_duration': 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(dt):
    return dt.strftime('%H:%M')

def can_meet(start, end, min_duration):
    duration = (end - start).seconds // 60
    return duration >= min_duration

def find_optimal_schedule():
    current_location = 'Russian Hill'
    current_time = parse_time('9:00')
    itinerary = []

    def add_meeting(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": time_to_str(start),
            "end_time": time_to_str(end)
        })

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)

        if arrival_time < start:
            meeting_start = start
        else:
            meeting_start = arrival_time

        meeting_end = meeting_start + timedelta(minutes=min_duration)

        if can_meet(meeting_start, end, min_duration):
            add_meeting(person, location, meeting_start, meeting_end)
            current_location = location
            current_time = meeting_end
        else:
            # If we can't meet the required duration, skip this meeting
            continue

    return itinerary

optimal_schedule = find_optimal_schedule()
result = {"itinerary": optimal_schedule}
print(json.dumps(result))