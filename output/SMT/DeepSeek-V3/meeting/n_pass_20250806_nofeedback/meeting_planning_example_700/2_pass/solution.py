from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their details
    friends = [
        {"name": "Kevin", "location": "Pacific Heights", "start": "7:15", "end": "8:45", "duration": 90},
        {"name": "Michelle", "location": "Golden Gate Park", "start": "20:00", "end": "21:00", "duration": 15},
        {"name": "Emily", "location": "Fisherman's Wharf", "start": "16:15", "end": "19:00", "duration": 30},
        {"name": "Mark", "location": "Marina District", "start": "18:15", "end": "19:45", "duration": 75},
        {"name": "Barbara", "location": "Alamo Square", "start": "17:00", "end": "19:00", "duration": 120},
        {"name": "Laura", "location": "Sunset District", "start": "19:00", "end": "21:15", "duration": 75},
        {"name": "Mary", "location": "Nob Hill", "start": "17:30", "end": "19:00", "duration": 45},
        {"name": "Helen", "location": "North Beach", "start": "11:00", "end": "12:15", "duration": 45}
    ]

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
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])
        friend['var_start'] = Int(f"start_{friend['name']}")
        friend['var_end'] = Int(f"end_{friend['name']}")
        s.add(friend['var_start'] >= friend['start_min'])
        s.add(friend['var_end'] <= friend['end_min'])
        s.add(friend['var_end'] == friend['var_start'] + friend['duration'])
        s.add(friend['var_start'] >= 540)  # Cannot start before 9:00 AM

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Presidio": {
            "Pacific Heights": 11,
            "Golden Gate Park": 12,
            "Fisherman's Wharf": 19,
            "Marina District": 11,
            "Alamo Square": 19,
            "Sunset District": 15,
            "Nob Hill": 18,
            "North Beach": 18
        },
        "Pacific Heights": {
            "Presidio": 11,
            "Golden Gate Park": 15,
            "Fisherman's Wharf": 13,
            "Marina District": 6,
            "Alamo Square": 10,
            "Sunset District": 21,
            "Nob Hill": 8,
            "North Beach": 9
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Pacific Heights": 16,
            "Fisherman's Wharf": 24,
            "Marina District": 16,
            "Alamo Square": 9,
            "Sunset District": 10,
            "Nob Hill": 20,
            "North Beach": 23
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Pacific Heights": 12,
            "Golden Gate Park": 25,
            "Marina District": 9,
            "Alamo Square": 21,
            "Sunset District": 27,
            "Nob Hill": 11,
            "North Beach": 6
        },
        "Marina District": {
            "Presidio": 10,
            "Pacific Heights": 7,
            "Golden Gate Park": 18,
            "Fisherman's Wharf": 10,
            "Alamo Square": 15,
            "Sunset District": 19,
            "Nob Hill": 12,
            "North Beach": 11
        },
        "Alamo Square": {
            "Presidio": 17,
            "Pacific Heights": 10,
            "Golden Gate Park": 9,
            "Fisherman's Wharf": 19,
            "Marina District": 15,
            "Sunset District": 16,
            "Nob Hill": 11,
            "North Beach": 15
        },
        "Sunset District": {
            "Presidio": 16,
            "Pacific Heights": 21,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 29,
            "Marina District": 21,
            "Alamo Square": 17,
            "Nob Hill": 27,
            "North Beach": 28
        },
        "Nob Hill": {
            "Presidio": 17,
            "Pacific Heights": 8,
            "Golden Gate Park": 17,
            "Fisherman's Wharf": 10,
            "Marina District": 11,
            "Alamo Square": 11,
            "Sunset District": 24,
            "North Beach": 8
        },
        "North Beach": {
            "Presidio": 17,
            "Pacific Heights": 8,
            "Golden Gate Park": 22,
            "Fisherman's Wharf": 5,
            "Marina District": 9,
            "Alamo Square": 16,
            "Sunset District": 27,
            "Nob Hill": 7
        }
    }

    # Define the order of meetings (heuristic approach)
    # We'll try to meet friends in the order of their availability and travel feasibility
    # This is a simplified approach; a full solution would explore all permutations
    meeting_order = ["Helen", "Mary", "Barbara", "Emily", "Mark", "Laura", "Michelle"]

    # Initialize current location and time
    current_location = "Presidio"
    current_time = 540  # 9:00 AM

    itinerary = []

    for friend_name in meeting_order:
        friend = next(f for f in friends if f['name'] == friend_name)
        travel_time = travel_times[current_location][friend['location']]
        s.push()
        s.add(friend['var_start'] >= current_time + travel_time)
        if s.check() == sat:
            m = s.model()
            start = m[friend['var_start']].as_long()
            end = m[friend['var_end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
            current_location = friend['location']
            current_time = end
        else:
            s.pop()

    # Output the itinerary
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

solve_scheduling()