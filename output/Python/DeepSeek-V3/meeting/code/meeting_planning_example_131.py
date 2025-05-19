import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%-H:%M')

def compute_schedule():
    # Input parameters
    travel_times = {
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Marina District'): 6,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Marina District'): 10,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Presidio'): 10,
    }
    
    # Constraints
    start_location = 'Pacific Heights'
    start_time = parse_time('9:00')
    
    jason_location = 'Presidio'
    jason_window_start = parse_time('10:00')
    jason_window_end = parse_time('16:15')
    jason_duration = timedelta(minutes=90)
    
    kenneth_location = 'Marina District'
    kenneth_window_start = parse_time('15:30')
    kenneth_window_end = parse_time('16:45')
    kenneth_duration = timedelta(minutes=45)
    
    # Possible schedules
    possible_schedules = []
    
    # Option 1: Meet Jason first, then Kenneth
    # Calculate earliest arrival at Presidio
    travel_to_jason = travel_times[(start_location, jason_location)]
    arrival_jason = start_time + timedelta(minutes=travel_to_jason)
    meet_jason_start = max(arrival_jason, jason_window_start)
    meet_jason_end = meet_jason_start + jason_duration
    if meet_jason_end <= jason_window_end:
        # Travel to Kenneth
        travel_to_kenneth = travel_times[(jason_location, kenneth_location)]
        arrival_kenneth = meet_jason_end + timedelta(minutes=travel_to_kenneth)
        meet_kenneth_start = max(arrival_kenneth, kenneth_window_start)
        meet_kenneth_end = meet_kenneth_start + kenneth_duration
        if meet_kenneth_end <= kenneth_window_end:
            possible_schedules.append([
                {'action': 'meet', 'location': jason_location, 'person': 'Jason', 
                 'start_time': format_time(meet_jason_start), 'end_time': format_time(meet_jason_end)},
                {'action': 'meet', 'location': kenneth_location, 'person': 'Kenneth', 
                 'start_time': format_time(meet_kenneth_start), 'end_time': format_time(meet_kenneth_end)}
            ])
    
    # Option 2: Meet Kenneth first, then Jason
    # Calculate earliest arrival at Marina District
    travel_to_kenneth = travel_times[(start_location, kenneth_location)]
    arrival_kenneth = start_time + timedelta(minutes=travel_to_kenneth)
    meet_kenneth_start = max(arrival_kenneth, kenneth_window_start)
    meet_kenneth_end = meet_kenneth_start + kenneth_duration
    if meet_kenneth_end <= kenneth_window_end:
        # Travel to Jason
        travel_to_jason = travel_times[(kenneth_location, jason_location)]
        arrival_jason = meet_kenneth_end + timedelta(minutes=travel_to_jason)
        meet_jason_start = max(arrival_jason, jason_window_start)
        meet_jason_end = meet_jason_start + jason_duration
        if meet_jason_end <= jason_window_end:
            possible_schedules.append([
                {'action': 'meet', 'location': kenneth_location, 'person': 'Kenneth', 
                 'start_time': format_time(meet_kenneth_start), 'end_time': format_time(meet_kenneth_end)},
                {'action': 'meet', 'location': jason_location, 'person': 'Jason', 
                 'start_time': format_time(meet_jason_start), 'end_time': format_time(meet_jason_end)}
            ])
    
    # Select the best schedule (prefer meeting both if possible)
    best_schedule = []
    if len(possible_schedules) > 0:
        # Prefer schedules where both meetings happen
        valid_schedules = [s for s in possible_schedules if len(s) == 2]
        if valid_schedules:
            best_schedule = valid_schedules[0]
        else:
            # Fallback to meeting just one person
            for s in possible_schedules:
                if len(s) == 1:
                    best_schedule = s
                    break
    
    return {'itinerary': best_schedule}

if __name__ == '__main__':
    schedule = compute_schedule()
    print(json.dumps(schedule, indent=2))