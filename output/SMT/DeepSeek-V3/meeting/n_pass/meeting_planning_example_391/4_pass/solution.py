from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define all time points in minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM at Sunset District

    # Meeting duration requirements
    durations = {
        'kevin': 75,
        'kimberly': 30,
        'joseph': 45,
        'thomas': 45
    }

    # Availability windows
    availability = {
        'kevin': (8*60 + 15, 21*60 + 30),    # 8:15 AM - 9:30 PM
        'kimberly': (8*60 + 45, 12*60 + 30),  # 8:45 AM - 12:30 PM
        'joseph': (18*60 + 30, 19*60 + 15),   # 6:30 PM - 7:15 PM
        'thomas': (19*60, 21*60 + 45)         # 7:00 PM - 9:45 PM
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('sunset', 'alamo'): 17,
        ('alamo', 'russian'): 13,
        ('russian', 'presidio'): 14,
        ('presidio', 'financial'): 23
    }

    # Create variables for each meeting
    meetings = {}
    for name in durations:
        meetings[name] = {
            'start': Int(f'{name}_start'),
            'end': Int(f'{name}_end'),
            'location': {
                'kevin': 'alamo',
                'kimberly': 'russian',
                'joseph': 'presidio',
                'thomas': 'financial'
            }[name]
        }

    # Add basic meeting constraints
    for name in meetings:
        m = meetings[name]
        s.add(m['start'] >= availability[name][0])
        s.add(m['end'] <= availability[name][1])
        s.add(m['end'] == m['start'] + durations[name])

    # Define meeting sequence and travel constraints
    current_time = arrival_time
    current_location = 'sunset'
    
    meeting_order = ['kevin', 'kimberly', 'joseph', 'thomas']
    
    for name in meeting_order:
        m = meetings[name]
        travel_key = (current_location, m['location'])
        travel_time = travel_times[travel_key]
        
        # Add travel time constraint
        s.add(m['start'] >= current_time + travel_time)
        
        # Update current time and location
        current_time = m['end']
        current_location = m['location']

    # Check for solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            ampm = "AM" if h < 12 else "PM"
            h = h if h <= 12 else h - 12
            return f"{h}:{m:02d} {ampm}"
        
        for name in meeting_order:
            start = m.evaluate(meetings[name]['start']).as_long()
            end = m.evaluate(meetings[name]['end']).as_long()
            location = meetings[name]['location'].capitalize() + (' Square' if name == 'kevin' else ' Hill' if name == 'kimberly' else '')
            
            print(f"Meet {name.capitalize()} at {location} from {format_time(start)} to {format_time(end)}")
    else:
        print("No valid schedule found.")

solve_scheduling()