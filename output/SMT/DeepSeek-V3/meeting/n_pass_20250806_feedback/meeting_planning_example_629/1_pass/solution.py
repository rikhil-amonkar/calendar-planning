from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {"name": "Matthew", "location": "Presidio", "available_start": "11:00", "available_end": "21:00", "min_duration": 90},
        {"name": "Margaret", "location": "Chinatown", "available_start": "09:15", "available_end": "18:45", "min_duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "available_start": "14:15", "available_end": "17:00", "min_duration": 15},
        {"name": "Helen", "location": "Richmond District", "available_start": "19:45", "available_end": "22:00", "min_duration": 60},
        {"name": "Rebecca", "location": "Fisherman's Wharf", "available_start": "21:15", "available_end": "22:15", "min_duration": 60},
        {"name": "Kimberly", "location": "Golden Gate Park", "available_start": "13:00", "available_end": "16:30", "min_duration": 120},
        {"name": "Kenneth", "location": "Bayview", "available_start": "14:30", "available_end": "18:00", "min_duration": 60}
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Russian Hill": {
            "Presidio": 14,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "Richmond District": 14,
            "Fisherman's Wharf": 7,
            "Golden Gate Park": 21,
            "Bayview": 23
        },
        "Presidio": {
            "Russian Hill": 14,
            "Chinatown": 21,
            "Pacific Heights": 11,
            "Richmond District": 7,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 12,
            "Bayview": 31
        },
        "Chinatown": {
            "Russian Hill": 7,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Richmond District": 20,
            "Fisherman's Wharf": 8,
            "Golden Gate Park": 23,
            "Bayview": 22
        },
        "Pacific Heights": {
            "Russian Hill": 7,
            "Presidio": 11,
            "Chinatown": 11,
            "Richmond District": 12,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15,
            "Bayview": 22
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Presidio": 7,
            "Chinatown": 20,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 18,
            "Golden Gate Park": 9,
            "Bayview": 26
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "Richmond District": 18,
            "Golden Gate Park": 25,
            "Bayview": 26
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16,
            "Richmond District": 7,
            "Fisherman's Wharf": 24,
            "Bayview": 23
        },
        "Bayview": {
            "Russian Hill": 23,
            "Presidio": 31,
            "Chinatown": 18,
            "Pacific Heights": 23,
            "Richmond District": 25,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22
        }
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting's start and end times
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend["min_duration"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        
        # Add constraints for meeting times
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + duration)
        s.add(start >= 0)
        
        meeting_vars.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "duration": duration
        })

    # Add constraints for travel times between consecutive meetings
    for i in range(len(meeting_vars)):
        for j in range(len(meeting_vars)):
            if i != j:
                loc_i = meeting_vars[i]["location"]
                loc_j = meeting_vars[j]["location"]
                travel_time = travel_times[loc_i][loc_j]
                s.add(Or(
                    meeting_vars[j]["start"] >= meeting_vars[i]["end"] + travel_time,
                    meeting_vars[i]["start"] >= meeting_vars[j]["end"] + travel_time
                ))

    # Add constraint to start at Russian Hill at 9:00 AM (0 minutes)
    # The first meeting must start after travel time from Russian Hill
    for i in range(len(meeting_vars)):
        loc = meeting_vars[i]["location"]
        travel_time = travel_times["Russian Hill"][loc]
        s.add(meeting_vars[i]["start"] >= travel_time)

    # Try to maximize the number of meetings (soft constraint)
    # We'll prioritize longer meetings first
    # This is a heuristic to help the solver find a feasible solution
    # Z3 doesn't directly support maximizing the number of satisfied constraints,
    # so we'll rely on the order of assertions and the solver's heuristics

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meeting_vars:
            start_val = model[meeting["start"]].as_long()
            end_val = model[meeting["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))