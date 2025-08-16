import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Sunset District'): 17,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Sunset District'): 19,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Sunset District'): 15,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Sunset District'): 27,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Sunset District'): 30,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Richmond District'): 9,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Sunset District'): 11,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Sunset District'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
}

# Define the meetings constraints
meetings = {
    'Elizabeth': {'location': 'Marina District', 'start': '19:00', 'end': '20:45', 'min_duration': 105},
    'Joshua': {'location': 'Presidio', 'start': '8:30', 'end': '13:15', 'min_duration': 105},
    'Timothy': {'location': 'North Beach', 'start': '19:45', 'end': '22:00', 'min_duration': 90},
    'David': {'location': 'Embarcadero', 'start': '10:45', 'end': '12:30', 'min_duration': 30},
    'Kimberly': {'location': 'Haight-Ashbury', 'start': '16:45', 'end': '21:30', 'min_duration': 75},
    'Lisa': {'location': 'Golden Gate Park', 'start': '17:30', 'end': '21:45', 'min_duration': 45},
    'Ronald': {'location': 'Richmond District', 'start': '8:00', 'end': '9:30', 'min_duration': 90},
    'Stephanie': {'location': 'Alamo Square', 'start': '15:30', 'end': '16:30', 'min_duration': 30},
    'Helen': {'location': 'Financial District', 'start': '17:30', 'end': '18:30', 'min_duration': 45},
    'Laura': {'location': 'Sunset District', 'start': '17:45', 'end': '21:15', 'min_duration': 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

def time_diff(start, end):
    start_dt = datetime.combine(datetime.today(), start)
    end_dt = datetime.combine(datetime.today(), end)
    return (end_dt - start_dt).seconds // 60

def can_meet(meeting, current_time):
    start = parse_time(meeting['start'])
    end = parse_time(meeting['end'])
    return start <= current_time < end

def find_next_meeting(current_location, current_time):
    available_meetings = []
    for person, meeting in meetings.items():
        if can_meet(meeting, current_time):
            travel_time = travel_times.get((current_location, meeting['location']), float('inf'))
            available_meetings.append((meeting, travel_time))
    
    available_meetings.sort(key=lambda x: x[1])  # Sort by travel time
    
    for meeting, travel_time in available_meetings:
        start = parse_time(meeting['start'])
        end = parse_time(meeting['end'])
        min_duration = meeting['min_duration']
        
        # Calculate the earliest possible start time after travel
        earliest_start = datetime.combine(datetime.today(), current_time) + timedelta(minutes=travel_time)
        earliest_start_time = earliest_start.time()
        
        # Check if we can meet for the required duration
        if earliest_start_time <= end and time_diff(earliest_start_time, end) >= min_duration:
            return meeting, travel_time, earliest_start_time
    
    return None, None, None

def create_schedule():
    itinerary = []
    current_location = 'The Castro'
    current_time = parse_time('9:00')
    
    while True:
        next_meeting, travel_time, start_time = find_next_meeting(current_location, current_time)
        if next_meeting is None:
            # No more meetings can be attended, move to the next hour
            current_time = (datetime.combine(datetime.today(), current_time) + timedelta(hours=1)).time()
            if current_time.hour >= 24:  # If it's past midnight, stop the loop
                break
            continue
        
        end_time = datetime.combine(datetime.today(), start_time) + timedelta(minutes=next_meeting['min_duration'])
        end_time = end_time.time()
        
        if travel_time > 0:
            itinerary.append({
                "action": "travel",
                "location": next_meeting['location'],
                "person": None,
                "start_time": current_time.strftime('%H:%M'),
                "end_time": (datetime.combine(datetime.today(), current_time) + timedelta(minutes=travel_time)).time().strftime('%H:%M')
            })
            current_time = (datetime.combine(datetime.today(), current_time) + timedelta(minutes=travel_time)).time()
        
        itinerary.append({
            "action": "meet",
            "location": next_meeting['location'],
            "person": list(meetings.keys())[list(meetings.values()).index(next_meeting)],
            "start_time": start_time.strftime('%H:%M'),
            "end_time": end_time.strftime('%H:%M')
        })
        
        current_location = next_meeting['location']
        current_time = end_time
    
    return itinerary

schedule = create_schedule()
result = {"itinerary": schedule}
print(json.dumps(result, indent=2))