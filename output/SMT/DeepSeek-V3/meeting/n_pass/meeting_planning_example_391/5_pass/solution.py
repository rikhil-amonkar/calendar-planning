from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define all time points in minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM at Sunset District

    # Meeting information
    meetings = {
        'kevin': {
            'duration': 75,
            'available_start': 8*60 + 15,  # 8:15 AM
            'available_end': 21*60 + 30,   # 9:30 PM
            'location': 'alamo'
        },
        'kimberly': {
            'duration': 30,
            'available_start': 8*60 + 45,  # 8:45 AM
            'available_end': 12*60 + 30,   # 12:30 PM
            'location': 'russian'
        },
        'joseph': {
            'duration': 45,
            'available_start': 18*60 + 30,  # 6:30 PM
            'available_end': 19*60 + 15,    # 7:15 PM
            'location': 'presidio'
        },
        'thomas': {
            'duration': 45,
            'available_start': 19*60,       # 7:00 PM
            'available_end': 21*60 + 45,    # 9:45 PM
            'location': 'financial'
        }
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('sunset', 'alamo'): 17,
        ('alamo', 'russian'): 13,
        ('russian', 'presidio'): 14,
        ('presidio', 'financial'): 23
    }

    # Create variables for each meeting
    for name in meetings:
        meetings[name]['start'] = Int(f'{name}_start')
        meetings[name]['end'] = Int(f'{name}_end')

    # Add basic meeting constraints
    for name in meetings:
        m = meetings[name]
        s.add(m['start'] >= m['available_start'])
        s.add(m['end'] <= m['available_end'])
        s.add(m['end'] == m['start'] + m['duration'])

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
            start_val = m[meetings[name]['start']]
            end_val = m[meetings[name]['end']]
            
            # Safely convert model values to integers
            start = start_val.as_long() if is_int_value(start_val) else 0
            end = end_val.as_long() if is_int_value(end_val) else 0
            
            location_name = {
                'alamo': 'Alamo Square',
                'russian': 'Russian Hill',
                'presidio': 'Presidio',
                'financial': 'Financial District'
            }[meetings[name]['location']]
            
            print(f"Meet {name.capitalize()} at {location_name} from {format_time(start)} to {format_time(end)}")
    else:
        print("No valid schedule found.")

def is_int_value(val):
    # Helper function to check if a value is an integer
    return val is not None and hasattr(val, 'as_long')

solve_scheduling()