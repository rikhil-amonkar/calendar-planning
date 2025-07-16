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

    # Locations and travel times (in minutes)
    locations = {
        'sunset': 0,
        'alamo': 1,
        'russian': 2,
        'presidio': 3,
        'financial': 4
    }

    travel_times = {
        (0,1): 17,  # sunset -> alamo
        (1,2): 13,  # alamo -> russian
        (2,3): 14,  # russian -> presidio
        (3,4): 23   # presidio -> financial
    }

    # Create variables for each meeting
    meetings = {}
    for name in durations:
        meetings[name] = {
            'start': Int(f'{name}_start'),
            'end': Int(f'{name}_end'),
            'loc': {
                'kevin': 1,
                'kimberly': 2,
                'joseph': 3,
                'thomas': 4
            }[name]
        }

    # Add basic meeting constraints
    for name in meetings:
        m = meetings[name]
        s.add(m['start'] >= availability[name][0])
        s.add(m['end'] <= availability[name][1])
        s.add(m['end'] == m['start'] + durations[name])

    # Define meeting sequence and travel constraints
    # Start at Sunset District (location 0)
    current_time = arrival_time
    current_loc = 0

    # Meeting order: Kevin -> Kimberly -> Joseph -> Thomas
    meeting_order = ['kevin', 'kimberly', 'joseph', 'thomas']
    
    for name in meeting_order:
        m = meetings[name]
        # Add travel time constraint
        travel_time = travel_times[(current_loc, m['loc'])]
        s.add(m['start'] >= current_time + travel_time)
        # Update current time and location
        current_time = m['end']
        current_loc = m['loc']

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
            start = m[meetings[name]['start']].as_long()
            end = m[meetings[name]['end']].as_long()
            location = {
                1: "Alamo Square",
                2: "Russian Hill",
                3: "Presidio",
                4: "Financial District"
            }[meetings[name]['loc']]
            
            print(f"Meet {name.capitalize()} at {location} from {format_time(start)} to {format_time(end)}")
    else:
        print("No valid schedule found.")

solve_scheduling()