from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Matthew", "location": "The Castro", "available_start": "16:30", "available_end": "20:00", "min_duration": 45},
        {"name": "Rebecca", "location": "Nob Hill", "available_start": "15:15", "available_end": "19:15", "min_duration": 105},
        {"name": "Brian", "location": "Marina District", "available_start": "14:15", "available_end": "22:00", "min_duration": 30},
        {"name": "Emily", "location": "Pacific Heights", "available_start": "11:15", "available_end": "19:45", "min_duration": 15},
        {"name": "Karen", "location": "Haight-Ashbury", "available_start": "11:45", "available_end": "17:30", "min_duration": 30},
        {"name": "Stephanie", "location": "Mission District", "available_start": "13:00", "available_end": "15:45", "min_duration": 75},
        {"name": "James", "location": "Chinatown", "available_start": "14:30", "available_end": "19:00", "min_duration": 120},
        {"name": "Steven", "location": "Russian Hill", "available_start": "14:00", "available_end": "20:00", "min_duration": 30},
        {"name": "Elizabeth", "location": "Alamo Square", "available_start": "13:00", "available_end": "17:15", "min_duration": 120},
        {"name": "William", "location": "Bayview", "available_start": "18:15", "available_end": "20:15", "min_duration": 90}
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
    meeting_starts = {}
    meeting_ends = {}
    for friend in friends:
        name = friend["name"]
        meeting_starts[name] = Int(f'start_{name}')
        meeting_ends[name] = Int(f'end_{name}')

    # Add constraints for each friend's meeting time
    for friend in friends:
        name = friend["name"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        s.add(meeting_starts[name] >= available_start)
        s.add(meeting_ends[name] <= available_end)
        s.add(meeting_ends[name] == meeting_starts[name] + min_duration)

    # Define travel times between locations
    travel_times = {
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Bayview"): 27,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Bayview"): 22,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Bayview"): 14,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Bayview"): 20,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "The Castro"): 18,
        ("Russian Hill", "Bayview"): 23,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "The Castro"): 16,
        ("Nob Hill", "Bayview"): 19,
        ("Marina District", "The Castro"): 21,
        ("Marina District", "Bayview"): 27,
        ("The Castro", "Bayview"): 19
    }

    # Define a possible meeting order (heuristic)
    meeting_order = ["Emily", "Karen", "Stephanie", "Elizabeth", "James", "Steven", "Rebecca", "Brian", "Matthew", "William"]

    # Add travel time constraints between consecutive meetings
    prev_location = "Richmond District"
    for i in range(len(meeting_order)):
        current_person = meeting_order[i]
        current_location = next(f["location"] for f in friends if f["name"] == current_person)
        if i == 0:
            # First meeting starts after travel from Richmond District
            s.add(meeting_starts[current_person] >= 540 + travel_times[(prev_location, current_location)])
        else:
            prev_person = meeting_order[i-1]
            prev_location_prev = next(f["location"] for f in friends if f["name"] == prev_person)
            s.add(meeting_starts[current_person] >= meeting_ends[prev_person] + travel_times[(prev_location_prev, current_location)])
        prev_location = current_location

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            start = model.evaluate(meeting_starts[name]).as_long()
            end = model.evaluate(meeting_ends[name]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the scheduling problem
solution = solve_scheduling()
print(json.dumps(solution, indent=2))