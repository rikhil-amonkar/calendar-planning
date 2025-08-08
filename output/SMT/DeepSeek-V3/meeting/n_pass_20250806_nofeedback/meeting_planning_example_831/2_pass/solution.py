from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Friends and their details
    friends = {
        "Jeffrey": {"location": "Fisherman's Wharf", "start": "10:15", "end": "13:00", "min_duration": 90},
        "Ronald": {"location": "Alamo Square", "start": "07:45", "end": "14:45", "min_duration": 120},
        "Jason": {"location": "Financial District", "start": "10:45", "end": "16:00", "min_duration": 105},
        "Melissa": {"location": "Union Square", "start": "17:45", "end": "18:15", "min_duration": 15},
        "Elizabeth": {"location": "Sunset District", "start": "14:45", "end": "17:30", "min_duration": 105},
        "Margaret": {"location": "Embarcadero", "start": "13:15", "end": "19:00", "min_duration": 90},
        "George": {"location": "Golden Gate Park", "start": "19:00", "end": "22:00", "min_duration": 75},
        "Richard": {"location": "Chinatown", "start": "09:30", "end": "21:00", "min_duration": 15},
        "Laura": {"location": "Richmond District", "start": "09:45", "end": "18:00", "min_duration": 60}
    }

    # Travel times (simplified as a dictionary of dictionaries)
    travel_times = {
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Alamo Square": 19,
            "Financial District": 23,
            "Union Square": 22,
            "Sunset District": 15,
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Chinatown": 21,
            "Richmond District": 7
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Alamo Square": 21,
            "Financial District": 11,
            "Union Square": 13,
            "Sunset District": 27,
            "Embarcadero": 8,
            "Golden Gate Park": 25,
            "Chinatown": 12,
            "Richmond District": 18
        },
        "Alamo Square": {
            "Presidio": 17,
            "Fisherman's Wharf": 19,
            "Financial District": 17,
            "Union Square": 14,
            "Sunset District": 16,
            "Embarcadero": 16,
            "Golden Gate Park": 9,
            "Chinatown": 15,
            "Richmond District": 11
        },
        "Financial District": {
            "Presidio": 22,
            "Fisherman's Wharf": 10,
            "Alamo Square": 17,
            "Union Square": 9,
            "Sunset District": 30,
            "Embarcadero": 4,
            "Golden Gate Park": 23,
            "Chinatown": 5,
            "Richmond District": 21
        },
        "Union Square": {
            "Presidio": 24,
            "Fisherman's Wharf": 15,
            "Alamo Square": 15,
            "Financial District": 9,
            "Sunset District": 27,
            "Embarcadero": 11,
            "Golden Gate Park": 22,
            "Chinatown": 7,
            "Richmond District": 20
        },
        "Sunset District": {
            "Presidio": 16,
            "Fisherman's Wharf": 29,
            "Alamo Square": 17,
            "Financial District": 30,
            "Union Square": 30,
            "Embarcadero": 30,
            "Golden Gate Park": 11,
            "Chinatown": 30,
            "Richmond District": 12
        },
        "Embarcadero": {
            "Presidio": 20,
            "Fisherman's Wharf": 6,
            "Alamo Square": 19,
            "Financial District": 5,
            "Union Square": 10,
            "Sunset District": 30,
            "Golden Gate Park": 25,
            "Chinatown": 7,
            "Richmond District": 21
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Fisherman's Wharf": 24,
            "Alamo Square": 9,
            "Financial District": 26,
            "Union Square": 22,
            "Sunset District": 10,
            "Embarcadero": 25,
            "Chinatown": 23,
            "Richmond District": 7
        },
        "Chinatown": {
            "Presidio": 19,
            "Fisherman's Wharf": 8,
            "Alamo Square": 17,
            "Financial District": 5,
            "Union Square": 7,
            "Sunset District": 29,
            "Embarcadero": 5,
            "Golden Gate Park": 23,
            "Richmond District": 20
        },
        "Richmond District": {
            "Presidio": 7,
            "Fisherman's Wharf": 18,
            "Alamo Square": 13,
            "Financial District": 22,
            "Union Square": 21,
            "Sunset District": 11,
            "Embarcadero": 19,
            "Golden Gate Park": 9,
            "Chinatown": 20
        }
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
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"{name}_start")
        end_var = Int(f"{name}_end")
        meeting_vars[name] = (start_var, end_var)

    # Add constraints for each friend's availability and duration
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]
        start_var, end_var = meeting_vars[name]

        # Meeting must be within friend's availability
        s.add(start_var >= start_min)
        s.add(end_var <= end_min)
        s.add(end_var >= start_var + min_duration)

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Presidio"

    # We'll allow the solver to choose the order of meetings
    # Define a list of all friends
    all_friends = list(friends.keys())

    # Define a variable to indicate if a friend is visited
    visited = {name: Bool(f"visited_{name}") for name in all_friends}

    # Define the order of visits as a list of integers
    order = [Int(f"order_{i}") for i in range(len(all_friends))]

    # Each order position must be between 0 and len(all_friends) - 1
    for o in order:
        s.add(o >= 0)
        s.add(o < len(all_friends))

    # All order positions must be distinct
    s.add(Distinct(order))

    # Define the start and end times for each visit
    prev_end = current_time
    prev_location = current_location
    for i in range(len(all_friends)):
        # Get the friend at this position in the order
        friend_idx = order[i]
        friend_name = all_friends[friend_idx]
        start_var, end_var = meeting_vars[friend_name]
        friend_loc = friends[friend_name]["location"]
        travel_time = travel_times[prev_location][friend_loc]

        # Add constraints for travel time and meeting time
        s.add(Implies(visited[friend_name], start_var >= prev_end + travel_time))
        s.add(Implies(visited[friend_name], end_var == start_var + friends[friend_name]["min_duration"]))
        prev_end = end_var
        prev_location = friend_loc

    # Maximize the number of friends visited
    s.maximize(Sum([If(visited[name], 1, 0) for name in all_friends]))

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Determine the order of visits from the model
        visit_order = sorted([(model.evaluate(order[i]).as_long(), all_friends[i]) for i in range(len(all_friends))], key=lambda x: x[0])
        for idx, name in visit_order:
            if model.evaluate(visited[name]):
                start_var, end_var = meeting_vars[name]
                start_time = model.evaluate(start_var).as_long()
                end_time = model.evaluate(end_var).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the scheduling problem
solution = solve_scheduling()
print(json.dumps(solution, indent=2))