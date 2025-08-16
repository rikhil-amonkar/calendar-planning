import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def find_meeting_times(constraints, min_duration):
    start = parse_time(constraints['start'])
    end = parse_time(constraints['end'])
    duration = timedelta(minutes=min_duration)
    possible_meetings = []
    current_time = start
    while current_time + duration <= end:
        possible_meetings.append((current_time, current_time + duration))
        current_time += timedelta(minutes=1)
    return possible_meetings

def calculate_travel_time(start_location, end_location, travel_times):
    return timedelta(minutes=travel_times[(start_location, end_location)])

def find_optimal_schedule():
    start_time = parse_time('9:00')
    locations = ['Embarcadero', 'Financial District', 'Alamo Square']
    travel_times = {
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Alamo Square'): 17,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Financial District'): 17
    }
    constraints = {
        'Stephanie': {'location': 'Financial District', 'start': '8:15', 'end': '11:30', 'min_duration': 90},
        'John': {'location': 'Alamo Square', 'start': '10:15', 'end': '20:45', 'min_duration': 30}
    }
    
    stephanie_meetings = find_meeting_times(constraints['Stephanie'], constraints['Stephanie']['min_duration'])
    john_meetings = find_meeting_times(constraints['John'], constraints['John']['min_duration'])
    
    best_schedule = None
    best_score = float('-inf')
    
    for stephanie_start, stephanie_end in stephanie_meetings:
        for john_start, john_end in john_meetings:
            # Try to fit both meetings starting from Embarcadero
            current_time = start_time
            schedule = []
            
            # Go to Stephanie
            travel_to_stephanie = calculate_travel_time('Embarcadero', 'Financial District', travel_times)
            if current_time + travel_to_stephanie > stephanie_start:
                continue
            current_time += travel_to_stephanie
            if current_time < stephanie_start:
                current_time = stephanie_start
            schedule.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Stephanie",
                "start_time": format_time(current_time),
                "end_time": format_time(stephanie_end)
            })
            current_time = stephanie_end
            
            # Go to John
            travel_to_john = calculate_travel_time('Financial District', 'Alamo Square', travel_times)
            if current_time + travel_to_john > john_start:
                continue
            current_time += travel_to_john
            if current_time < john_start:
                current_time = john_start
            schedule.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "John",
                "start_time": format_time(current_time),
                "end_time": format_time(john_end)
            })
            current_time = john_end
            
            # Calculate score (earlier finish time is better)
            score = - (current_time - start_time).total_seconds()
            if score > best_score:
                best_score = score
                best_schedule = schedule
    
    # Try reverse order: John first, then Stephanie
    for john_start, john_end in john_meetings:
        for stephanie_start, stephanie_end in stephanie_meetings:
            current_time = start_time
            schedule = []
            
            # Go to John
            travel_to_john = calculate_travel_time('Embarcadero', 'Alamo Square', travel_times)
            if current_time + travel_to_john > john_start:
                continue
            current_time += travel_to_john
            if current_time < john_start:
                current_time = john_start
            schedule.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "John",
                "start_time": format_time(current_time),
                "end_time": format_time(john_end)
            })
            current_time = john_end
            
            # Go to Stephanie
            travel_to_stephanie = calculate_travel_time('Alamo Square', 'Financial District', travel_times)
            if current_time + travel_to_stephanie > stephanie_start:
                continue
            current_time += travel_to_stephanie
            if current_time < stephanie_start:
                current_time = stephanie_start
            schedule.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Stephanie",
                "start_time": format_time(current_time),
                "end_time": format_time(stephanie_end)
            })
            current_time = stephanie_end
            
            # Calculate score (earlier finish time is better)
            score = - (current_time - start_time).total_seconds()
            if score > best_score:
                best_score = score
                best_schedule = schedule
    
    return {"itinerary": best_schedule}

print(json.dumps(find_optimal_schedule()))