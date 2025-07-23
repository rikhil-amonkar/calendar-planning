import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16
}

# Define meeting constraints
meetings = {
    'David': {'location': 'Fisherman\'s Wharf', 'start': '10:45', 'end': '15:30', 'min_duration': 15},
    'Timothy': {'location': 'Pacific Heights', 'start': '09:00', 'end': '15:30', 'min_duration': 75},
    'Robert': {'location': 'Mission District', 'start': '12:15', 'end': '19:45', 'min_duration': 90}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_schedule():
    start_time = parse_time('9:00')
    current_location = 'Financial District'
    itinerary = []

    def visit(person, location, start, end, min_duration):
        nonlocal start_time, current_location, itinerary
        start_time = max(start_time, parse_time(start))
        travel_time = travel_times[(current_location, location)]
        start_time = add_minutes(start_time, travel_time)
        if can_meet(start_time.strftime('%H:%M'), end, min_duration):
            end_time = add_minutes(start_time, min_duration).strftime('%H:%M')
            if parse_time(end_time) <= parse_time(end):
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": start_time.strftime('%H:%M'),
                    "end_time": end_time
                })
                start_time = parse_time(end_time)
                current_location = location
            else:
                print(f"Cannot meet {person} within the available time window.")
        else:
            print(f"Not enough time to meet {person} for the required duration.")

    # Try to meet Timothy first due to his long required meeting time
    visit('Timothy', meetings['Timothy']['location'], meetings['Timothy']['start'], meetings['Timothy']['end'], meetings['Timothy']['min_duration'])
    
    # Try to meet David next
    visit('David', meetings['David']['location'], meetings['David']['start'], meetings['David']['end'], meetings['David']['min_duration'])
    
    # Finally, try to meet Robert
    visit('Robert', meetings['Robert']['location'], meetings['Robert']['start'], meetings['Robert']['end'], meetings['Robert']['min_duration'])

    return itinerary

itinerary = find_schedule()
output = {"itinerary": itinerary}
print(json.dumps(output))