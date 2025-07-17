from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Initialize solver with optimization
    opt = Optimize()

    friends = [
        {"name": "Lisa", "location": "The Castro", "start": "19:15", "end": "21:15", "min_duration": 120},
        {"name": "Daniel", "location": "Nob Hill", "start": "08:15", "end": "11:00", "min_duration": 15},
        {"name": "Elizabeth", "location": "Presidio", "start": "21:15", "end": "22:15", "min_duration": 45},
        {"name": "Steven", "location": "Marina District", "start": "16:30", "end": "20:45", "min_duration": 90},
        {"name": "Timothy", "location": "Pacific Heights", "start": "12:00", "end": "18:00", "min_duration": 90},
        {"name": "Ashley", "location": "Golden Gate Park", "start": "20:45", "end": "21:45", "min_duration": 60},
        {"name": "Kevin", "location": "Chinatown", "start": "12:00", "end": "19:00", "min_duration": 30},
        {"name": "Betty", "location": "Richmond District", "start": "13:15", "end": "15:45", "min_duration": 30}
    ]

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    travel_times = {
        "Mission District": {"The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19, 
                            "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20},
        "The Castro": {"Mission District": 7, "Nob Hill": 16, "Presidio": 20, "Marina District": 21, 
                      "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16},
        "Nob Hill": {"Mission District": 13, "The Castro": 17, "Presidio": 17, "Marina District": 11, 
                    "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14},
        "Presidio": {"Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 11, 
                    "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7},
        "Marina District": {"Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10, 
                          "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11},
        "Pacific Heights": {"Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11, 
                          "Marina District": 6, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12},
        "Golden Gate Park": {"Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11, 
                           "Marina District": 16, "Pacific Heights": 16, "Chinatown": 23, "Richmond District": 7},
        "Chinatown": {"Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19, 
                     "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Richmond District": 20},
        "Richmond District": {"Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7, 
                            "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20}
    }

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend['min_duration']
        window_start = time_to_minutes(friend['start'])
        window_end = time_to_minutes(friend['end'])
        
        opt.add(start >= window_start)
        opt.add(end <= window_end)
        opt.add(end == start + duration)
        
        meetings.append({
            "name": friend['name'],
            "location": friend['location'],
            "start": start,
            "end": end,
            "duration": duration
        })

    # Initial condition: start at Mission District at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Mission District"

    # Create variables to represent meeting order
    n = len(meetings)
    order = [Int(f"order_{i}") for i in range(n)]
    
    # Each order variable must be between 0 and n-1
    for o in order:
        opt.add(o >= 0)
        opt.add(o < n)
    
    # All order variables must be distinct
    opt.add(Distinct(order))
    
    # Create variables for the start time of each meeting in the schedule
    scheduled_starts = [Int(f"scheduled_start_{i}") for i in range(n)]
    scheduled_ends = [Int(f"scheduled_end_{i}") for i in range(n)]
    locations = [m['location'] for m in meetings]
    
    # Link order variables to actual meetings
    for i in range(n):
        for j in range(n):
            opt.add(Implies(order[i] == j, scheduled_starts[i] == meetings[j]['start']))
            opt.add(Implies(order[i] == j, scheduled_ends[i] == meetings[j]['end']))
    
    # Add travel time constraints
    prev_end = current_time
    prev_location = current_location
    for i in range(n):
        travel_time = Int(f"travel_{i}")
        # Get travel time from previous location to current meeting location
        for loc in travel_times.keys():
            for meeting in meetings:
                opt.add(Implies(And(order[i] == meetings.index(meeting), prev_location == loc),
                              travel_time == travel_times[loc][meeting['location']]))
        
        opt.add(scheduled_starts[i] >= prev_end + travel_time)
        prev_end = scheduled_ends[i]
        prev_location = locations[order[i].as_long() if isinstance(order[i], int) else 0]  # Approximation
    
    # Optimization objective: maximize total meeting time
    total_time = Int('total_time')
    opt.add(total_time == sum([m['duration'] for m in meetings]))
    opt.maximize(total_time)

    # Check if the schedule is feasible
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for meeting in meetings:
            start_val = model.evaluate(meeting['start']).as_long()
            end_val = model.evaluate(meeting['end']).as_long()
            scheduled_meetings.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": scheduled_meetings}
    else:
        return {"error": "No feasible schedule found."}

# Run the solver and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))