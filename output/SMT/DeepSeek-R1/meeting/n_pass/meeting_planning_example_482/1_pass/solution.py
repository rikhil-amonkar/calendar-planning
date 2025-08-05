from z3 import *
import json

def main():
    # Initialize solver
    s = Solver()
    
    # Friends to meet (excluding Richard because it's impossible)
    friends = ['Stephanie', 'Sandra', 'Brian', 'Jason']
    
    # Minimum meeting durations in minutes
    min_dur = {
        'Stephanie': 90,
        'Sandra': 15,
        'Brian': 120,
        'Jason': 60
    }
    
    # Availability windows in minutes from 9:00 AM (0 minutes = 9:00 AM)
    avail_start = {
        'Stephanie': -45,  # 8:15 AM
        'Sandra': 240,     # 1:00 PM
        'Brian': 195,      # 12:15 PM
        'Jason': -30       # 8:30 AM
    }
    
    avail_end = {
        'Stephanie': 285,  # 1:45 PM
        'Sandra': 630,     # 7:30 PM
        'Brian': 420,      # 4:00 PM
        'Jason': 525       # 5:45 PM
    }
    
    # Locations of each friend
    loc = {
        'Stephanie': 'Mission District',
        'Sandra': 'Bayview',
        'Brian': 'Russian Hill',
        'Jason': "Fisherman's Wharf"
    }
    
    # Travel time matrix
    travel = {
        'Haight-Ashbury': {
            'Mission District': 11,
            'Bayview': 18,
            'Russian Hill': 17,
            "Fisherman's Wharf": 23
        },
        'Mission District': {
            'Haight-Ashbury': 12,
            'Bayview': 15,
            'Russian Hill': 15,
            "Fisherman's Wharf": 22
        },
        'Bayview': {
            'Haight-Ashbury': 19,
            'Mission District': 13,
            'Russian Hill': 23,
            "Fisherman's Wharf": 25
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Bayview': 23,
            "Fisherman's Wharf": 7
        },
        "Fisherman's Wharf": {
            'Haight-Ashbury': 22,
            'Mission District': 22,
            'Bayview': 26,
            'Russian Hill': 7
        }
    }
    
    # Create Z3 variables
    meet_vars = {f: Bool(f"meet_{f}") for f in friends}
    start_vars = {f: Real(f"start_{f}") for f in friends}
    pos_vars = {f: Int(f"pos_{f}") for f in friends}
    
    # Constraint: All meetings are scheduled
    for f in friends:
        s.add(meet_vars[f] == True)
    
    # Constraint: Positions are distinct and between 0 and 3
    s.add(Distinct([pos_vars[f] for f in friends]))
    for f in friends:
        s.add(pos_vars[f] >= 0)
        s.add(pos_vars[f] < 4)
    
    # Constraint: At least one meeting has position 0
    s.add(Or([pos_vars[f] == 0 for f in friends]))
    
    # Constraints for each friend
    for f in friends:
        # If meeting is scheduled, it must be within availability window
        s.add(If(meet_vars[f], start_vars[f] >= avail_start[f], True))
        s.add(If(meet_vars[f], start_vars[f] + min_dur[f] <= avail_end[f], True))
        
        # First meeting must account for travel from start location
        s.add(If(And(meet_vars[f], pos_vars[f] == 0), 
                start_vars[f] >= travel['Haight-Ashbury'][loc[f]], 
                True))
        
        # Subsequent meetings must account for travel from previous location
        for g in friends:
            if f == g:
                continue
            s.add(If(And(meet_vars[f], meet_vars[g], pos_vars[f] > 0, pos_vars[g] == pos_vars[f] - 1),
                   start_vars[f] >= start_vars[g] + min_dur[g] + travel[loc[g]][loc[f]],
                   True))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Collect meetings with their positions
        meetings = []
        for f in friends:
            if model.eval(meet_vars[f]):
                start_val = model.eval(start_vars[f])
                # Convert Z3 rational to float
                if is_rational_value(start_val):
                    start_min = float(start_val.as_fraction())
                else:
                    start_min = float(start_val.as_decimal(10))
                end_min = start_min + min_dur[f]
                pos = model.eval(pos_vars[f]).as_long()
                meetings.append((pos, f, start_min, end_min))
        
        # Sort meetings by position
        meetings.sort(key=lambda x: x[0])
        
        # Convert minutes to HH:MM format
        for pos, f, start_min, end_min in meetings:
            # Convert minutes from 9:00 AM to time
            start_time = (9 * 60 + start_min) % (24 * 60)
            end_time = (9 * 60 + end_min) % (24 * 60)
            start_hour = int(start_time // 60)
            start_minute = int(start_time % 60)
            end_hour = int(end_time // 60)
            end_minute = int(end_time % 60)
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": f,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output in JSON format
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()