from z3 import *
import json

def main():
    meetings = ['Rebecca', 'Stephanie', 'Karen', 'Brian', 'Steven']
    locations = {
        'Rebecca': "Fisherman's Wharf",
        'Stephanie': 'Golden Gate Park',
        'Karen': 'Chinatown',
        'Brian': 'Union Square',
        'Steven': 'North Beach'
    }
    
    # Convert times to minutes from 9:00 AM
    available_start = {
        'Rebecca': 15,    # 9:15 AM
        'Stephanie': 60,   # 10:00 AM
        'Karen': 240,      # 1:00 PM
        'Brian': 360,      # 3:00 PM
        'Steven': 0        # Available after 9:00 AM
    }
    
    available_end = {
        'Rebecca': 135,    # 11:15 AM
        'Stephanie': 360,  # 3:00 PM
        'Karen': 450,      # 4:30 PM
        'Brian': 495,      # 5:15 PM
        'Steven': 705      # 8:45 PM
    }
    
    min_duration = {
        'Rebecca': 30,
        'Stephanie': 105,
        'Karen': 15,
        'Brian': 30,
        'Steven': 120
    }
    
    # Travel times between locations (in minutes)
    travel_dict = {
        'Financial District': {
            "Fisherman's Wharf": 10,
            'Golden Gate Park': 23,
            'Chinatown': 5,
            'Union Square': 9,
            'North Beach': 7
        },
        "Fisherman's Wharf": {
            'Golden Gate Park': 25,
            'Chinatown': 12,
            'Union Square': 13,
            'North Beach': 6
        },
        'Golden Gate Park': {
            "Fisherman's Wharf": 24,
            'Chinatown': 23,
            'Union Square': 22,
            'North Beach': 24
        },
        'Chinatown': {
            "Fisherman's Wharf": 8,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'North Beach': 3
        },
        'Union Square': {
            "Fisherman's Wharf": 15,
            'Golden Gate Park': 22,
            'Chinatown': 7,
            'North Beach': 10
        },
        'North Beach': {
            "Fisherman's Wharf": 5,
            'Golden Gate Park': 22,
            'Chinatown': 6,
            'Union Square': 7
        }
    }
    
    # Create Z3 solver
    s = Solver()
    
    # Create variables for start and end times (in minutes from 9:00 AM)
    start_vars = {name: Int(f's_{name}') for name in meetings}
    end_vars = {name: Int(f'e_{name}') for name in meetings}
    
    # Add constraints for each meeting
    for name in meetings:
        # Start time must be after availability begins
        s.add(start_vars[name] >= available_start[name])
        # End time must be before availability ends
        s.add(end_vars[name] <= available_end[name])
        # Meeting duration constraint
        s.add(end_vars[name] - start_vars[name] >= min_duration[name])
        # Ensure positive duration
        s.add(start_vars[name] <= end_vars[name])
    
    # First meeting must account for travel from Financial District
    s.add(start_vars['Rebecca'] >= travel_dict['Financial District'][locations['Rebecca']])
    
    # Meeting sequence constraints with travel times
    s.add(start_vars['Stephanie'] >= end_vars['Rebecca'] + travel_dict[locations['Rebecca']][locations['Stephanie']])
    s.add(start_vars['Karen'] >= end_vars['Stephanie'] + travel_dict[locations['Stephanie']][locations['Karen']])
    s.add(start_vars['Brian'] >= end_vars['Karen'] + travel_dict[locations['Karen']][locations['Brian']])
    s.add(start_vars['Steven'] >= end_vars['Brian'] + travel_dict[locations['Brian']][locations['Steven']])
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in meetings:
            s_val = m.eval(start_vars[name]).as_long()
            e_val = m.eval(end_vars[name]).as_long()
            # Convert minutes to time string
            start_hour = 9 + s_val // 60
            start_min = s_val % 60
            end_hour = 9 + e_val // 60
            end_min = e_val % 60
            start_str = f"{start_hour:02d}:{start_min:02d}"
            end_str = f"{end_hour:02d}:{end_min:02d}"
            schedule.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output itinerary
        print("SOLUTION:")
        print(json.dumps({"itinerary": schedule}, indent=2))
    else:
        print("No valid schedule found")

if __name__ == '__main__':
    main()