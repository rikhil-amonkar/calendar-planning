import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%-H:%M')

def calculate_schedule():
    # Input parameters
    travel_times = {
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Financial District'): 20,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Financial District'): 17,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Mission District'): 17
    }
    
    current_location = 'The Castro'
    current_time = parse_time('9:00')
    
    laura_location = 'Mission District'
    laura_start = parse_time('12:15')
    laura_end = parse_time('19:45')
    laura_min_duration = timedelta(minutes=75)
    
    anthony_location = 'Financial District'
    anthony_start = parse_time('12:30')
    anthony_end = parse_time('14:45')
    anthony_min_duration = timedelta(minutes=30)
    
    itinerary = []
    
    # Calculate possible meeting with Anthony
    # Option 1: Meet Anthony first
    travel_to_anthony = travel_times[(current_location, anthony_location)]
    earliest_arrival_anthony = current_time + timedelta(minutes=travel_to_anthony)
    
    meet_anthony_start = max(earliest_arrival_anthony, anthony_start)
    meet_anthony_end = min(meet_anthony_start + anthony_min_duration, anthony_end)
    
    if meet_anthony_end <= anthony_end and (meet_anthony_end - meet_anthony_start) >= anthony_min_duration:
        # Then try to meet Laura
        travel_to_laura = travel_times[(anthony_location, laura_location)]
        earliest_arrival_laura = meet_anthony_end + timedelta(minutes=travel_to_laura)
        
        meet_laura_start = max(earliest_arrival_laura, laura_start)
        meet_laura_end = min(meet_laura_start + laura_min_duration, laura_end)
        
        if meet_laura_end <= laura_end and (meet_laura_end - meet_laura_start) >= laura_min_duration:
            itinerary = [
                {
                    "action": "meet",
                    "location": anthony_location,
                    "person": "Anthony",
                    "start_time": format_time(meet_anthony_start),
                    "end_time": format_time(meet_anthony_end)
                },
                {
                    "action": "meet",
                    "location": laura_location,
                    "person": "Laura",
                    "start_time": format_time(meet_laura_start),
                    "end_time": format_time(meet_laura_end)
                }
            ]
            return itinerary
    
    # Option 2: Meet Laura first
    travel_to_laura = travel_times[(current_location, laura_location)]
    earliest_arrival_laura = current_time + timedelta(minutes=travel_to_laura)
    
    meet_laura_start = max(earliest_arrival_laura, laura_start)
    meet_laura_end = min(meet_laura_start + laura_min_duration, laura_end)
    
    if meet_laura_end <= laura_end and (meet_laura_end - meet_laura_start) >= laura_min_duration:
        # Then try to meet Anthony
        travel_to_anthony = travel_times[(laura_location, anthony_location)]
        earliest_arrival_anthony = meet_laura_end + timedelta(minutes=travel_to_anthony)
        
        meet_anthony_start = max(earliest_arrival_anthony, anthony_start)
        meet_anthony_end = min(meet_anthony_start + anthony_min_duration, anthony_end)
        
        if meet_anthony_end <= anthony_end and (meet_anthony_end - meet_anthony_start) >= anthony_min_duration:
            itinerary = [
                {
                    "action": "meet",
                    "location": laura_location,
                    "person": "Laura",
                    "start_time": format_time(meet_laura_start),
                    "end_time": format_time(meet_laura_end)
                },
                {
                    "action": "meet",
                    "location": anthony_location,
                    "person": "Anthony",
                    "start_time": format_time(meet_anthony_start),
                    "end_time": format_time(meet_anthony_end)
                }
            ]
            return itinerary
    
    # If both options fail, try to meet just one person
    # Try Laura first
    travel_to_laura = travel_times[(current_location, laura_location)]
    earliest_arrival_laura = current_time + timedelta(minutes=travel_to_laura)
    
    meet_laura_start = max(earliest_arrival_laura, laura_start)
    meet_laura_end = min(meet_laura_start + laura_min_duration, laura_end)
    
    if meet_laura_end <= laura_end and (meet_laura_end - meet_laura_start) >= laura_min_duration:
        itinerary = [
            {
                "action": "meet",
                "location": laura_location,
                "person": "Laura",
                "start_time": format_time(meet_laura_start),
                "end_time": format_time(meet_laura_end)
            }
        ]
        return itinerary
    
    # Then try Anthony
    travel_to_anthony = travel_times[(current_location, anthony_location)]
    earliest_arrival_anthony = current_time + timedelta(minutes=travel_to_anthony)
    
    meet_anthony_start = max(earliest_arrival_anthony, anthony_start)
    meet_anthony_end = min(meet_anthony_start + anthony_min_duration, anthony_end)
    
    if meet_anthony_end <= anthony_end and (meet_anthony_end - meet_anthony_start) >= anthony_min_duration:
        itinerary = [
            {
                "action": "meet",
                "location": anthony_location,
                "person": "Anthony",
                "start_time": format_time(meet_anthony_start),
                "end_time": format_time(meet_anthony_end)
            }
        ]
        return itinerary
    
    return []

result = calculate_schedule()
output = {"itinerary": result}
print(json.dumps(output, indent=2))