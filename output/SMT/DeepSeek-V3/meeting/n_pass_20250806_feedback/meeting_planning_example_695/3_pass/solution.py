from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints
    friends = [
        {"name": "Paul", "location": "Nob Hill", "start_window": "16:15", "end_window": "21:15", "min_duration": 60},
        {"name": "Carol", "location": "Union Square", "start_window": "18:00", "end_window": "20:15", "min_duration": 120},
        {"name": "Patricia", "location": "Chinatown", "start_window": "20:00", "end_window": "21:30", "min_duration": 75},
        {"name": "Karen", "location": "The Castro", "start_window": "17:00", "end_window": "19:00", "min_duration": 45},
        {"name": "Nancy", "location": "Presidio", "start_window": "11:45", "end_window": "22:00", "min_duration": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "start_window": "20:00", "end_window": "20:45", "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "start_window": "15:45", "end_window": "21:45", "min_duration": 75}
    ]

    # Travel times between locations (in minutes)
    travel_times = {
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "The Castro"): 20,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Russian Hill"): 23,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Nob Hill"): 8,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Chinatown"): 20,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Russian Hill"): 14,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Pacific Heights"): 7
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        friend['start_var'] = start_var
        friend['end_var'] = end_var

        # Meeting must be within the friend's window
        window_start = time_to_minutes(friend['start_window'])
        window_end = time_to_minutes(friend['end_window'])
        s.add(start_var >= window_start)
        s.add(end_var <= window_end)
        s.add(end_var >= start_var + friend['min_duration'])

    # Define the order of meetings to account for travel times
    # We'll choose an order that minimizes travel time conflicts
    meeting_order = ["Nancy", "Matthew", "Paul", "Karen", "Carol", "Patricia", "Jeffrey"]

    # Ensure that the end time of one meeting plus travel time to the next does not exceed the start time of the next
    for i in range(len(meeting_order) - 1):
        current_friend = next(f for f in friends if f['name'] == meeting_order[i])
        next_friend = next(f for f in friends if f['name'] == meeting_order[i + 1])
        travel_time = travel_times[(current_friend['location'], next_friend['location'])]
        s.add(next_friend['start_var'] >= current_friend['end_var'] + travel_time)

    # Try to meet all friends
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start_val = model[friend['start_var']].as_long()
            end_val = model[friend['end_var']].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing constraints or adjusting the order
        # For simplicity, we'll return an empty itinerary
        return {"itinerary": []}

# Run the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))