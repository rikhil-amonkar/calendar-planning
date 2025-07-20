from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

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
        "Mission District": {"The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19, "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20},
        "The Castro": {"Mission District": 7, "Nob Hill": 16, "Presidio": 20, "Marina District": 21, "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16},
        "Nob Hill": {"Mission District": 13, "The Castro": 17, "Presidio": 17, "Marina District": 11, "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14},
        "Presidio": {"Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 11, "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7},
        "Marina District": {"Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10, "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11},
        "Pacific Heights": {"Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11, "Marina District": 6, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12},
        "Golden Gate Park": {"Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11, "Marina District": 16, "Pacific Heights": 16, "Chinatown": 23, "Richmond District": 7},
        "Chinatown": {"Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19, "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Richmond District": 20},
        "Richmond District": {"Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7, "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20}
    }

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend['min_duration']
        window_start = time_to_minutes(friend['start'])
        window_end = time_to_minutes(friend['end'])
        
        s.add(start >= window_start)
        s.add(end <= window_end)
        s.add(end == start + duration)
        
        meetings.append({
            "name": friend['name'],
            "location": friend['location'],
            "start": start,
            "end": end
        })

    # Initial condition: start at Mission District at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Mission District"

    # We need to sequence the meetings. To model this, we can use a permutation of the meetings.
    # However, modeling permutations in Z3 is complex. Instead, we'll assume an order and add constraints.
    # For this problem, let's try to meet Daniel first, then Betty, Kevin, Timothy, Steven, Ashley, Lisa, Elizabeth.

    # Define the order (heuristic)
    order = ["Daniel", "Betty", "Kevin", "Timothy", "Steven", "Ashley", "Lisa", "Elizabeth"]
    ordered_meetings = []
    for name in order:
        for m in meetings:
            if m['name'] == name:
                ordered_meetings.append(m)
                break

    # Add travel time constraints between consecutive meetings
    prev_end = current_time
    prev_location = current_location
    for meeting in ordered_meetings:
        travel_time = travel_times[prev_location][meeting['location']]
        s.add(meeting['start'] >= prev_end + travel_time)
        prev_end = meeting['end']
        prev_location = meeting['location']

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
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