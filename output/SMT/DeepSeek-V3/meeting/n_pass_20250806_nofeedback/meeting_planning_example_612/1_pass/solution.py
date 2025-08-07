from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Emily": {"location": "Russian Hill", "start": "12:15", "end": "14:15", "min_duration": 105},
        "Mark": {"location": "Presidio", "start": "14:45", "end": "19:30", "min_duration": 60},
        "Deborah": {"location": "Chinatown", "start": "07:30", "end": "15:30", "min_duration": 45},
        "Margaret": {"location": "Sunset District", "start": "21:30", "end": "22:30", "min_duration": 60},
        "George": {"location": "The Castro", "start": "07:30", "end": "14:15", "min_duration": 60},
        "Andrew": {"location": "Embarcadero", "start": "20:15", "end": "22:00", "min_duration": 75},
        "Steven": {"location": "Golden Gate Park", "start": "11:15", "end": "21:15", "min_duration": 105}
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

    # Initialize variables for each meeting
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Add constraints for each meeting
    for name, info in friends.items():
        start_time = time_to_minutes(info["start"])
        end_time = time_to_minutes(info["end"])
        min_duration = info["min_duration"]

        s.add(meeting_vars[name]["start"] >= start_time)
        s.add(meeting_vars[name]["end"] <= end_time)
        s.add(meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration)

    # Initial location is Alamo Square at 9:00 AM (540 minutes)
    current_location = "Alamo Square"
    current_time = 540  # 9:00 AM in minutes

    # Define travel times (in minutes)
    travel_times = {
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Embarcadero"): 31,
        ("Sunset District", "Golden Gate Park"): 11,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Chinatown"): 20,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Golden Gate Park"): 11,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25,
    }

    # Define the order of meetings (this is a simplification; in reality, we'd need to model the order)
    # For simplicity, we'll assume a fixed order and add constraints accordingly
    # This is a heuristic approach; a more complete solution would involve modeling all possible orders
    # Here, we'll prioritize meeting friends with tighter time windows first

    # Define a possible order: George, Deborah, Steven, Emily, Mark, Andrew, Margaret
    order = ["George", "Deborah", "Steven", "Emily", "Mark", "Andrew", "Margaret"]

    # Add travel time constraints
    for i in range(len(order)):
        if i == 0:
            # First meeting: travel from Alamo Square to friend's location
            friend = order[i]
            location = friends[friend]["location"]
            travel_time = travel_times[(current_location, location)]
            s.add(meeting_vars[friend]["start"] >= current_time + travel_time)
        else:
            # Subsequent meetings: travel from previous friend's location to current friend's location
            prev_friend = order[i-1]
            prev_location = friends[prev_friend]["location"]
            current_friend = order[i]
            current_location_friend = friends[current_friend]["location"]
            travel_time = travel_times[(prev_location, current_location_friend)]
            s.add(meeting_vars[current_friend]["start"] >= meeting_vars[prev_friend]["end"] + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start = model[meeting_vars[name]["start"]].as_long()
            end = model[meeting_vars[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the scheduling problem
result = solve_scheduling()

# Print the result in JSON format
print(json.dumps(result, indent=2))