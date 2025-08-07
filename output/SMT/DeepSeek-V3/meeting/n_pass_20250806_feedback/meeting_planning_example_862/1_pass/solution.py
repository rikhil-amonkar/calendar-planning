import json
from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Laura": {"location": "Alamo Square", "start": "14:30", "end": "16:15", "min_duration": 75},
        "Brian": {"location": "Presidio", "start": "10:15", "end": "17:00", "min_duration": 30},
        "Karen": {"location": "Russian Hill", "start": "18:00", "end": "20:15", "min_duration": 90},
        "Stephanie": {"location": "North Beach", "start": "10:15", "end": "16:00", "min_duration": 75},
        "Helen": {"location": "Golden Gate Park", "start": "11:30", "end": "21:45", "min_duration": 120},
        "Sandra": {"location": "Richmond District", "start": "08:00", "end": "15:15", "min_duration": 30},
        "Mary": {"location": "Embarcadero", "start": "16:45", "end": "18:45", "min_duration": 120},
        "Deborah": {"location": "Financial District", "start": "19:00", "end": "20:45", "min_duration": 105},
        "Elizabeth": {"location": "Marina District", "start": "08:30", "end": "13:15", "min_duration": 105}
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

    # Current location starts at Mission District at 9:00 AM (540 minutes)
    current_location = "Mission District"
    current_time = 540  # 9:00 AM in minutes

    # Define travel times (in minutes) between locations
    travel_times = {
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Marina District"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Marina District"): 16,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Marina District"): 9,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17,
    }

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Add constraints for each meeting
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        s.add(meeting_vars[name]["start"] >= start_min)
        s.add(meeting_vars[name]["end"] <= end_min)
        s.add(meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration)

    # Add constraints for travel times between meetings
    # We need to ensure that the start time of the next meeting is after the end time of the previous meeting plus travel time
    # Since the order of meetings is not fixed, we'll need to model this as a disjunction of possible sequences
    # For simplicity, we'll assume a fixed order based on the availability windows
    # This is a heuristic and may not find the optimal solution, but it's a starting point

    # Define a possible order based on availability windows
    # We'll try to meet friends in the order of their availability windows
    ordered_friends = ["Elizabeth", "Sandra", "Brian", "Stephanie", "Laura", "Helen", "Mary", "Karen", "Deborah"]

    # Add constraints for travel times between meetings in the order
    for i in range(len(ordered_friends) - 1):
        current_friend = ordered_friends[i]
        next_friend = ordered_friends[i + 1]
        current_loc = friends[current_friend]["location"]
        next_loc = friends[next_friend]["location"]
        travel_time = travel_times.get((current_loc, next_loc), 0)  # Default to 0 if not found (shouldn't happen)
        s.add(meeting_vars[next_friend]["start"] >= meeting_vars[current_friend]["end"] + travel_time)

    # Also ensure the first meeting starts after the initial time plus travel time from Mission District
    first_friend = ordered_friends[0]
    first_loc = friends[first_friend]["location"]
    travel_time = travel_times.get(("Mission District", first_loc), 0)
    s.add(meeting_vars[first_friend]["start"] >= current_time + travel_time)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in ordered_friends:
            start = m.eval(meeting_vars[name]["start"]).as_long()
            end = m.eval(meeting_vars[name]["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))