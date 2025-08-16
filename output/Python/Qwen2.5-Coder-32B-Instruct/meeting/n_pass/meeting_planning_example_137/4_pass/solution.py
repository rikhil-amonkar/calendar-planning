import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def calculate_schedule():
    # Constants
    start_time = parse_time('9:00')
    end_time = parse_time('17:00')  # Assuming you want to be done by 5:00 PM
    travel_times = {
        ('Chinatown', 'Golden Gate Park'): timedelta(minutes=25),
        ('Golden Gate Park', 'Chinatown'): timedelta(minutes=25)
    }
    
    # Specific meeting times
    kenneth_start = parse_time('12:00')
    kenneth_end = parse_time('13:30')
    barbara_start = parse_time('16:15')
    barbara_end = parse_time('17:00')
    
    # Calculate the travel time from Chinatown to Golden Gate Park
    travel_time_1 = travel_times[('Chinatown', 'Golden Gate Park')]
    
    # Create the itinerary based on the specific meeting times
    itinerary = [
        {"action": "meet", "location": "Chinatown", "person": "Kenneth", "start_time": format_time(kenneth_start), "end_time": format_time(kenneth_end)},
        {"action": "travel", "location": "Golden Gate Park", "start_time": format_time(kenneth_end), "end_time": format_time(kenneth_end + travel_time_1)},
        {"action": "meet", "location": "Golden Gate Park", "person": "Barbara", "start_time": format_time(barbara_start), "end_time": format_time(barbara_end)}
    ]
    
    # Output the itinerary
    print(json.dumps({"itinerary": itinerary}))

calculate_schedule()