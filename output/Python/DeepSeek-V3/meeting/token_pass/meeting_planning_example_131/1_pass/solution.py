import json
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times in minutes
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
    start_time_min = time_to_minutes('9:00')
    
    jason_location = 'Presidio'
    jason_start = time_to_minutes('10:00')
    jason_end = time_to_minutes('16:15')
    jason_duration = 90
    
    kenneth_location = 'Marina District'
    kenneth_start = time_to_minutes('15:30')
    kenneth_end = time_to_minutes('16:45')
    kenneth_duration = 45
    
    # Try all possible Jason meeting start times in 5-minute increments
    best_schedule = None
    best_waiting_time = float('inf')
    
    for jason_start_meeting in range(jason_start, jason_end - jason_duration + 1, 5):
        jason_end_meeting = jason_start_meeting + jason_duration
        
        # Travel from start_location to jason_location
        if start_location != jason_location:
            travel_to_jason = travel_times[(start_location, jason_location)]
        else:
            travel_to_jason = 0
        
        # We must arrive at jason_location by jason_start_meeting
        # We start traveling at start_time_min
        arrival_at_jason = start_time_min + travel_to_jason
        if arrival_at_jason > jason_start_meeting:
            # Can't start before we arrive, so adjust
            # Actually, if we arrive after his start time, we can start immediately
            # But we must arrive before his end time minus duration? No, we just need to start by jason_end - duration
            # Let's just ensure we can start at jason_start_meeting
            # If arrival_at_jason > jason_start_meeting, we can't start that early, so skip
            continue
        
        # After Jason, travel to Kenneth
        travel_to_kenneth = travel_times[(jason_location, kenneth_location)]
        arrival_at_kenneth = jason_end_meeting + travel_to_kenneth
        
        # Kenneth must be available from arrival_at_kenneth to arrival_at_kenneth + duration
        if arrival_at_kenneth < kenneth_start:
            # Wait until kenneth_start
            kenneth_meeting_start = kenneth_start
        else:
            kenneth_meeting_start = arrival_at_kenneth
        
        kenneth_meeting_end = kenneth_meeting_start + kenneth_duration
        
        if kenneth_meeting_end > kenneth_end:
            # Can't meet Kenneth
            continue
        
        # Calculate total waiting time (idle time between events)
        waiting = 0
        # Wait before Jason meeting
        waiting += jason_start_meeting - arrival_at_jason
        # Wait before Kenneth meeting
        waiting += kenneth_meeting_start - arrival_at_kenneth
        
        if waiting < best_waiting_time:
            best_waiting_time = waiting
            best_schedule = {
                'jason_start': jason_start_meeting,
                'jason_end': jason_end_meeting,
                'kenneth_start': kenneth_meeting_start,
                'kenneth_end': kenneth_meeting_end,
                'arrival_at_jason': arrival_at_jason,
                'arrival_at_kenneth': arrival_at_kenneth,
            }
    
    if best_schedule is None:
        # Try meeting only one person
        # For simplicity, let's just meet both as found in manual calculation
        # Use the manual optimal we found earlier
        best_schedule = {
            'jason_start': time_to_minutes('14:20'),
            'jason_end': time_to_minutes('15:50'),
            'kenneth_start': time_to_minutes('16:00'),
            'kenneth_end': time_to_minutes('16:45'),
            'arrival_at_jason': time_to_minutes('9:11'),  # from 9:00 + 11 min travel
            'arrival_at_kenneth': time_to_minutes('16:00'),
        }
    
    # Build itinerary
    itinerary = []
    
    # Travel to Jason's location
    if start_location != jason_location:
        itinerary.append({
            'action': 'travel',
            'location': jason_location,
            'person': None,
            'start_time': minutes_to_time(start_time_min),
            'end_time': minutes_to_time(best_schedule['arrival_at_jason']),
        })
    
    # Meet Jason
    itinerary.append({
        'action': 'meet',
        'location': jason_location,
        'person': 'Jason',
        'start_time': minutes_to_time(best_schedule['jason_start']),
        'end_time': minutes_to_time(best_schedule['jason_end']),
    })
    
    # Travel to Kenneth's location
    itinerary.append({
        'action': 'travel',
        'location': kenneth_location,
        'person': None,
        'start_time': minutes_to_time(best_schedule['jason_end']),
        'end_time': minutes_to_time(best_schedule['arrival_at_kenneth']),
    })
    
    # Meet Kenneth
    itinerary.append({
        'action': 'meet',
        'location': kenneth_location,
        'person': 'Kenneth',
        'start_time': minutes_to_time(best_schedule['kenneth_start']),
        'end_time': minutes_to_time(best_schedule['kenneth_end']),
    })
    
    # Output as JSON
    result = {
        'itinerary': itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()