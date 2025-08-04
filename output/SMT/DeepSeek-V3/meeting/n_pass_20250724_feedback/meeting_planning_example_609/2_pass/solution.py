from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        "David": {
            "location": "Mission District",
            "available_start": 8 * 60,  # 8:00 AM in minutes
            "available_end": 19 * 60 + 45,  # 7:45 PM in minutes
            "min_duration": 45,
        },
        "Kenneth": {
            "location": "Alamo Square",
            "available_start": 14 * 60,  # 2:00 PM in minutes
            "available_end": 19 * 60 + 45,  # 7:45 PM in minutes
            "min_duration": 120,
        },
        "John": {
            "location": "Pacific Heights",
            "available_start": 17 * 60,  # 5:00 PM in minutes
            "available_end": 20 * 60,  # 8:00 PM in minutes
            "min_duration": 15,
        },
        "Charles": {
            "location": "Union Square",
            "available_start": 21 * 60 + 45,  # 9:45 PM in minutes
            "available_end": 22 * 60 + 45,  # 10:45 PM in minutes
            "min_duration": 60,
        },
        "Deborah": {
            "location": "Golden Gate Park",
            "available_start": 7 * 60,  # 7:00 AM in minutes
            "available_end": 18 * 60 + 15,  # 6:15 PM in minutes
            "min_duration": 90,
        },
        "Karen": {
            "location": "Sunset District",
            "available_start": 17 * 60 + 45,  # 5:45 PM in minutes
            "available_end": 21 * 60 + 15,  # 9:15 PM in minutes
            "min_duration": 15,
        },
        "Carol": {
            "location": "Presidio",
            "available_start": 8 * 60 + 15,  # 8:15 AM in minutes
            "available_end": 9 * 60 + 15,  # 9:15 AM in minutes
            "min_duration": 30,
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Chinatown": {
            "Mission District": 18,
            "Alamo Square": 17,
            "Pacific Heights": 10,
            "Union Square": 7,
            "Golden Gate Park": 23,
            "Sunset District": 29,
            "Presidio": 19,
        },
        "Mission District": {
            "Chinatown": 16,
            "Alamo Square": 11,
            "Pacific Heights": 16,
            "Union Square": 15,
            "Golden Gate Park": 17,
            "Sunset District": 24,
            "Presidio": 25,
        },
        "Alamo Square": {
            "Chinatown": 16,
            "Mission District": 10,
            "Pacific Heights": 10,
            "Union Square": 14,
            "Golden Gate Park": 9,
            "Sunset District": 16,
            "Presidio": 18,
        },
        "Pacific Heights": {
            "Chinatown": 11,
            "Mission District": 15,
            "Alamo Square": 10,
            "Union Square": 12,
            "Golden Gate Park": 15,
            "Sunset District": 21,
            "Presidio": 11,
        },
        "Union Square": {
            "Chinatown": 7,
            "Mission District": 14,
            "Alamo Square": 15,
            "Pacific Heights": 15,
            "Golden Gate Park": 22,
            "Sunset District": 26,
            "Presidio": 24,
        },
        "Golden Gate Park": {
            "Chinatown": 23,
            "Mission District": 17,
            "Alamo Square": 10,
            "Pacific Heights": 16,
            "Union Square": 22,
            "Sunset District": 10,
            "Presidio": 11,
        },
        "Sunset District": {
            "Chinatown": 30,
            "Mission District": 24,
            "Alamo Square": 17,
            "Pacific Heights": 21,
            "Union Square": 30,
            "Golden Gate Park": 11,
            "Presidio": 16,
        },
        "Presidio": {
            "Chinatown": 21,
            "Mission District": 26,
            "Alamo Square": 18,
            "Pacific Heights": 11,
            "Union Square": 22,
            "Golden Gate Park": 12,
            "Sunset District": 15,
        }
    }

    # Variables for each meeting: start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}
        # Constrain meeting to be within friend's availability
        s.add(start >= friends[name]["available_start"])
        s.add(end <= friends[name]["available_end"])
        s.add(end - start >= friends[name]["min_duration"])

    # Starting point: Chinatown at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = "Chinatown"

    # We'll try to meet Carol first since she's available early
    s.add(meeting_vars["Carol"]["start"] >= current_time)
    s.add(meeting_vars["Carol"]["end"] <= friends["Carol"]["available_end"])
    s.add(meeting_vars["Carol"]["end"] - meeting_vars["Carol"]["start"] >= friends["Carol"]["min_duration"])

    # After meeting Carol, we can meet others in any order, but we need to ensure travel times are accounted for
    # Let's define a sequence where each meeting's start time is after the previous meeting's end time plus travel time
    # We'll use a list to represent the order of meetings
    order = ["Carol", "David", "Deborah", "Kenneth", "John", "Karen", "Charles"]

    # Add constraints for the order
    prev_end = current_time
    prev_loc = current_location
    for name in order:
        if name in meeting_vars:
            meet = meeting_vars[name]
            # Travel time from previous location to current meeting location
            travel_time = travel_times[prev_loc][friends[name]["location"]]
            s.add(meet['start'] >= prev_end + travel_time)
            prev_end = meet['end']
            prev_loc = friends[name]["location"]

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            if name in meeting_vars:
                start_val = model[meeting_vars[name]['start']].as_long()
                end_val = model[meeting_vars[name]['end']].as_long()
                start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        return {"itinerary": itinerary}
    else:
        # If no solution found, try to meet fewer friends
        # For simplicity, we'll just return an empty itinerary
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))