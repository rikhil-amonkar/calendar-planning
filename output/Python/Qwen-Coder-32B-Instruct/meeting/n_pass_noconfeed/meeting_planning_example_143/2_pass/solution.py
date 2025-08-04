import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M').lstrip('0')

def find_meeting_schedule():
    # Input constraints
    arrival_time = parse_time('9:00')
    karen_start = parse_time('18:45')
    karen_end = parse_time('20:15')
    mark_start = parse_time('13:00')
    mark_end = parse_time('17:45')
    
    # Travel times in minutes
    travel_times = {
        ('North Beach', 'pacific heights'): 8,
        ('North Beach', 'embarcadero'): 6,
        ('pacific heights', 'north beach'): 9,
        ('pacific heights', 'embarcadero'): 10,
        ('embarcadero', 'north beach'): 5,
        ('embarcadero', 'pacific heights'): 11
    }
    
    # Minimum meeting durations in minutes
    min_meeting_durations = {
        'Karen': 90,
        'Mark': 120
    }
    
    # Possible meeting slots
    meeting_slots = {
        'Karen': [(karen_start, karen_end)],
        'Mark': [(mark_start, mark_end)]
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Try to meet Mark first if possible
    current_location = 'north beach'
    current_time = arrival_time
    
    def can_meet(person, slot):
        start, end = slot
        duration = (end - start).seconds // 60
        return duration >= min_meeting_durations[person]
    
    def add_meeting_to_itinerary(person, slot):
        nonlocal current_time, current_location
        start, end = slot
        travel_time = travel_times[(current_location, person.lower().replace(' ', ''))]
        start = max(start, current_time + timedelta(minutes=travel_time))
        end = min(end, start + timedelta(minutes=min_meeting_durations[person]))
        itinerary.append({
            "action": "meet",
            "location": person.lower().replace(' ', ''),
            "person": person,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
        current_time = end
        current_location = person.lower().replace(' ', '')
    
    for person, slots in meeting_slots.items():
        for slot in slots:
            if can_meet(person, slot):
                add_meeting_to_itinerary(person, slot)
                break
    
    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))