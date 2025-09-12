import itertools
from z3 import Real, Solver, sat

def main():
    # Travel times matrix
    travel_times = {
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Richmond District": 18,
            "Financial District": 11
        },
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Richmond District": 7,
            "Financial District": 23
        },
        "Richmond District": {
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Financial District": 22
        },
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Richmond District": 21
        }
    }
    
    # Meeting constraints
    meetings = [
        {
            "name": "Emily",
            "location": "Presidio",
            "duration": 105,
            "avail_start": 435,  # 4:15 PM in minutes from 9:00 AM
            "avail_end": 720     # 9:00 PM
        },
        {
            "name": "Joseph",
            "location": "Richmond District",
            "duration": 120,
            "avail_start": 495,  # 5:15 PM
            "avail_end": 780     # 10:00 PM
        },
        {
            "name": "Melissa",
            "location": "Financial District",
            "duration": 75,
            "avail_start": 405,  # 3:45 PM
            "avail_end": 765     # 9:45 PM
        }
    ]
    
    # Generate all possible meeting orders (1, 2, or 3 meetings)
    meeting_orders = []
    for r in range(3, 0, -1):
        meeting_orders.extend(itertools.permutations(meetings, r))
    
    # Try to find a feasible schedule
    schedule = None
    for order in meeting_orders:
        s = Solver()
        start_vars = [Real(f's{i}') for i in range(len(order))]
        
        # Add constraints for each meeting in the order
        prev_location = "Fisherman's Wharf"
        constraints = []
        for i, meeting in enumerate(order):
            # Travel time from previous location
            travel_time = travel_times[prev_location][meeting['location']]
            if i == 0:
                # First meeting must account for travel from start
                constraints.append(start_vars[i] >= travel_time)
            else:
                # Subsequent meetings must account for travel from previous meeting
                constraints.append(start_vars[i] >= start_vars[i-1] + order[i-1]['duration'] + travel_time)
            
            # Availability constraints
            constraints.append(start_vars[i] >= meeting['avail_start'])
            constraints.append(start_vars[i] + meeting['duration'] <= meeting['avail_end'])
            
            prev_location = meeting['location']
        
        # Check if constraints are satisfiable
        s.add(constraints)
        if s.check() == sat:
            m = s.model()
            start_times = [m.eval(var).as_long() for var in start_vars]
            schedule = []
            for i, meeting in enumerate(order):
                schedule.append({
                    "action": "meet",
                    "location": meeting['location'],
                    "person": meeting['name'],
                    "start_time": minutes_to_time(start_times[i]),
                    "end_time": minutes_to_time(start_times[i] + meeting['duration'])
                })
            break
    
    # Output result as JSON
    if schedule is None:
        print('{"itinerary": []}')
    else:
        import json
        output = {"itinerary": schedule}
        print(json.dumps(output))

def minutes_to_time(minutes):
    total_minutes = int(minutes)
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

if __name__ == "__main__":
    main()