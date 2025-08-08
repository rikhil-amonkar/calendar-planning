from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Thomas": {"location": "Bayview", "start": "15:30", "end": "18:30", "min_duration": 120},
        "Stephanie": {"location": "Golden Gate Park", "start": "18:30", "end": "21:45", "min_duration": 30},
        "Laura": {"location": "Nob Hill", "start": "08:45", "end": "16:15", "min_duration": 30},
        "Betty": {"location": "Marina District", "start": "18:45", "end": "21:45", "min_duration": 45},
        "Patricia": {"location": "Embarcadero", "start": "17:30", "end": "22:00", "min_duration": 45}
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

    # Current location starts at Fisherman's Wharf at 9:00 AM (540 minutes)
    current_location = "Fisherman's Wharf"
    current_time = time_to_minutes("09:00")

    # Define travel times (in minutes)
    travel_times = {
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Marina District"): 25,
        ("Bayview", "Embarcadero"): 19,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Embarcadero"): 9,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Embarcadero"): 14,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Marina District"): 12
    }

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        duration_var = Int(f"duration_{name}")
        meetings[name] = {
            "start": start_var,
            "end": end_var,
            "duration": duration_var,
            "location": friends[name]["location"],
            "min_duration": friends[name]["min_duration"],
            "available_start": time_to_minutes(friends[name]["start"]),
            "available_end": time_to_minutes(friends[name]["end"])
        }
        # Constraints: duration >= min_duration, start >= available_start, end <= available_end
        s.add(duration_var >= friends[name]["min_duration"])
        s.add(start_var >= meetings[name]["available_start"])
        s.add(end_var <= meetings[name]["available_end"])
        s.add(end_var == start_var + duration_var)

    # Define the order of meetings and travel times
    # We'll try to meet Laura first since she's available early
    # Then Thomas, Patricia, Betty, and Stephanie
    # This is a heuristic; the solver will adjust if needed

    # Meet Laura at Nob Hill
    laura_start = meetings["Laura"]["start"]
    laura_end = meetings["Laura"]["end"]
    travel_to_laura = travel_times[(current_location, "Nob Hill")]
    s.add(laura_start >= current_time + travel_to_laura)
    current_time = laura_end
    current_location = "Nob Hill"

    # Meet Thomas at Bayview
    thomas_start = meetings["Thomas"]["start"]
    thomas_end = meetings["Thomas"]["end"]
    travel_to_thomas = travel_times[(current_location, "Bayview")]
    s.add(thomas_start >= current_time + travel_to_thomas)
    current_time = thomas_end
    current_location = "Bayview"

    # Meet Patricia at Embarcadero
    patricia_start = meetings["Patricia"]["start"]
    patricia_end = meetings["Patricia"]["end"]
    travel_to_patricia = travel_times[(current_location, "Embarcadero")]
    s.add(patricia_start >= current_time + travel_to_patricia)
    current_time = patricia_end
    current_location = "Embarcadero"

    # Meet Betty at Marina District
    betty_start = meetings["Betty"]["start"]
    betty_end = meetings["Betty"]["end"]
    travel_to_betty = travel_times[(current_location, "Marina District")]
    s.add(betty_start >= current_time + travel_to_betty)
    current_time = betty_end
    current_location = "Marina District"

    # Meet Stephanie at Golden Gate Park
    stephanie_start = meetings["Stephanie"]["start"]
    stephanie_end = meetings["Stephanie"]["end"]
    travel_to_stephanie = travel_times[(current_location, "Golden Gate Park")]
    s.add(stephanie_start >= current_time + travel_to_stephanie)
    current_time = stephanie_end
    current_location = "Golden Gate Park"

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in meetings:
            start = model[meetings[name]["start"]].as_long()
            end = model[meetings[name]["end"]].as_long()
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

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))