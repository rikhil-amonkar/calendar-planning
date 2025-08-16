import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def calculate_schedule():
    # Constants
    start_time = parse_time('9:00')
    end_time = parse_time('17:00')  # Assuming you want to be done by 5:00 PM
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23
    }
    kenneth_start = parse_time('12:00')
    kenneth_end = parse_time('15:00')
    barbara_start = parse_time('8:15')
    barbara_end = parse_time('19:00')
    min_kenneth_meeting = timedelta(minutes=90)
    min_barbara_meeting = timedelta(minutes=45)

    # Possible meeting slots
    kenneth_slots = []
    current_time = kenneth_start
    while current_time + min_kenneth_meeting <= kenneth_end:
        kenneth_slots.append((current_time, current_time + min_kenneth_meeting))
        current_time += timedelta(minutes=1)

    barbara_slots = []
    current_time = barbara_start
    while current_time + min_barbara_meeting <= barbara_end:
        barbara_slots.append((current_time, current_time + min_barbara_meeting))
        current_time += timedelta(minutes=1)

    # Try to find the best schedule
    best_schedule = None
    best_duration = 0

    for k_start, k_end in kenneth_slots:
        for b_start, b_end in barbara_slots:
            # Check if both meetings can fit in the day
            if k_end + travel_times[('Chinatown', 'Golden Gate Park')] <= b_start:
                # Meeting Kenneth first, then Barbara
                schedule = [
                    {"action": "meet", "location": "Chinatown", "person": "Kenneth", "start_time": format_time(k_start), "end_time": format_time(k_end)},
                    {"action": "travel", "location": "Golden Gate Park", "start_time": format_time(k_end), "end_time": format_time(k_end + travel_times[('Chinatown', 'Golden Gate Park')])},
                    {"action": "meet", "location": "Golden Gate Park", "person": "Barbara", "start_time": format_time(b_start), "end_time": format_time(b_end)}
                ]
                total_duration = b_end - start_time
                if total_duration > best_duration and total_duration <= end_time - start_time:
                    best_duration = total_duration
                    best_schedule = schedule
            elif b_end + travel_times[('Golden Gate Park', 'Chinatown')] <= k_start:
                # Meeting Barbara first, then Kenneth
                schedule = [
                    {"action": "meet", "location": "Golden Gate Park", "person": "Barbara", "start_time": format_time(b_start), "end_time": format_time(b_end)},
                    {"action": "travel", "location": "Chinatown", "start_time": format_time(b_end), "end_time": format_time(b_end + travel_times[('Golden Gate Park', 'Chinatown')])},
                    {"action": "meet", "location": "Chinatown", "person": "Kenneth", "start_time": format_time(k_start), "end_time": format_time(k_end)}
                ]
                total_duration = k_end - start_time
                if total_duration > best_duration and total_duration <= end_time - start_time:
                    best_duration = total_duration
                    best_schedule = schedule

    # Output the best schedule found
    if best_schedule:
        print(json.dumps({"itinerary": best_schedule}))
    else:
        print(json.dumps({"itinerary": []}))

calculate_schedule()