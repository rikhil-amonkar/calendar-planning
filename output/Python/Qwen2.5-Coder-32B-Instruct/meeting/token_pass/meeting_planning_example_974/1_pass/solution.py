import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Sunset District': {'Presidio': 16, 'Nob Hill': 27, 'Pacific Heights': 21, 'Mission District': 25, 'Marina District': 21, 'North Beach': 28, 'Russian Hill': 24, 'Richmond District': 12, 'Embarcadero': 30, 'Alamo Square': 17},
    'Presidio': {'Sunset District': 15, 'Nob Hill': 18, 'Pacific Heights': 11, 'Mission District': 26, 'Marina District': 11, 'North Beach': 18, 'Russian Hill': 14, 'Richmond District': 7, 'Embarcadero': 20, 'Alamo Square': 19},
    'Nob Hill': {'Sunset District': 24, 'Presidio': 17, 'Pacific Heights': 8, 'Mission District': 13, 'Marina District': 11, 'North Beach': 8, 'Russian Hill': 5, 'Richmond District': 14, 'Embarcadero': 9, 'Alamo Square': 11},
    'Pacific Heights': {'Sunset District': 21, 'Presidio': 11, 'Nob Hill': 8, 'Mission District': 15, 'Marina District': 6, 'North Beach': 9, 'Russian Hill': 7, 'Richmond District': 12, 'Embarcadero': 10, 'Alamo Square': 10},
    'Mission District': {'Sunset District': 24, 'Presidio': 25, 'Nob Hill': 12, 'Pacific Heights': 16, 'Marina District': 19, 'North Beach': 17, 'Russian Hill': 15, 'Richmond District': 20, 'Embarcadero': 19, 'Alamo Square': 11},
    'Marina District': {'Sunset District': 19, 'Presidio': 10, 'Nob Hill': 12, 'Pacific Heights': 7, 'Mission District': 20, 'North Beach': 11, 'Russian Hill': 8, 'Richmond District': 11, 'Embarcadero': 14, 'Alamo Square': 15},
    'North Beach': {'Sunset District': 27, 'Presidio': 17, 'Nob Hill': 7, 'Pacific Heights': 8, 'Mission District': 18, 'Marina District': 11, 'Russian Hill': 4, 'Richmond District': 18, 'Embarcadero': 6, 'Alamo Square': 16},
    'Russian Hill': {'Sunset District': 23, 'Presidio': 14, 'Nob Hill': 5, 'Pacific Heights': 7, 'Mission District': 16, 'Marina District': 7, 'North Beach': 5, 'Richmond District': 14, 'Embarcadero': 8, 'Alamo Square': 15},
    'Richmond District': {'Sunset District': 11, 'Presidio': 7, 'Nob Hill': 17, 'Pacific Heights': 10, 'Mission District': 20, 'Marina District': 9, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19, 'Alamo Square': 13},
    'Embarcadero': {'Sunset District': 30, 'Presidio': 20, 'Nob Hill': 10, 'Pacific Heights': 11, 'Mission District': 20, 'Marina District': 12, 'North Beach': 5, 'Russian Hill': 8, 'Richmond District': 21, 'Alamo Square': 19},
    'Alamo Square': {'Sunset District': 16, 'Presidio': 17, 'Nob Hill': 11, 'Pacific Heights': 10, 'Mission District': 10, 'Marina District': 15, 'North Beach': 15, 'Russian Hill': 13, 'Richmond District': 11, 'Embarcadero': 16}
}

# Define meeting constraints
meetings = [
    {'name': 'Charles', 'location': 'Presidio', 'start': '13:15', 'end': '15:00', 'duration': 105},
    {'name': 'Robert', 'location': 'Nob Hill', 'start': '13:15', 'end': '17:30', 'duration': 90},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start': '14:45', 'end': '22:00', 'duration': 105},
    {'name': 'Brian', 'location': 'Mission District', 'start': '15:30', 'end': '22:00', 'duration': 60},
    {'name': 'Kimberly', 'location': 'Marina District', 'start': '17:00', 'end': '19:45', 'duration': 75},
    {'name': 'David', 'location': 'North Beach', 'start': '14:45', 'end': '16:30', 'duration': 75},
    {'name': 'William', 'location': 'Russian Hill', 'start': '12:30', 'end': '19:15', 'duration': 120},
    {'name': 'Jeffrey', 'location': 'Richmond District', 'start': '12:00', 'end': '19:15', 'duration': 45},
    {'name': 'Karen', 'location': 'Embarcadero', 'start': '14:15', 'end': '20:45', 'duration': 60},
    {'name': 'Joshua', 'location': 'Alamo Square', 'start': '18:45', 'end': '22:00', 'duration': 60}
]

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M')

def can_meet(current_time, meeting):
    meeting_start = parse_time(meeting['start'])
    meeting_end = parse_time(meeting['end'])
    required_end = current_time + timedelta(minutes=meeting['duration'])
    return meeting_start <= current_time <= meeting_end or meeting_start <= required_end <= meeting_end

def find_next_meeting(current_location, current_time):
    possible_meetings = []
    for meeting in meetings:
        if can_meet(current_time, meeting):
            travel_time = travel_times[current_location][meeting['location']]
            potential_start = current_time + timedelta(minutes=travel_time)
            if can_meet(potential_start, meeting):
                possible_meetings.append((meeting, travel_time))
    
    # Sort by longest meeting duration first
    possible_meetings.sort(key=lambda x: x[0]['duration'], reverse=True)
    return possible_meetings[0] if possible_meetings else None

def generate_schedule():
    itinerary = []
    current_location = 'Sunset District'
    current_time = parse_time('9:00')
    end_of_day = parse_time('24:00')
    
    while current_time < end_of_day:
        next_meeting_info = find_next_meeting(current_location, current_time)
        if not next_meeting_info:
            break
        
        next_meeting, travel_time = next_meeting_info
        travel_duration = timedelta(minutes=travel_time)
        meeting_start = current_time + travel_duration
        meeting_end = meeting_start + timedelta(minutes=next_meeting['duration'])
        
        itinerary.append({
            "action": "meet",
            "location": next_meeting['location'],
            "person": next_meeting['name'],
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        
        current_location = next_meeting['location']
        current_time = meeting_end
    
    return itinerary

schedule = generate_schedule()
output = {"itinerary": schedule}
print(json.dumps(output, indent=2))