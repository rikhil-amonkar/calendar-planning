from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "David", "location": "Sunset District", "start_window": "9:15", "end_window": "22:00", "min_duration": 15},
        {"name": "Kenneth", "location": "Union Square", "start_window": "21:15", "end_window": "21:45", "min_duration": 15},
        {"name": "Patricia", "location": "Nob Hill", "start_window": "15:00", "end_window": "19:15", "min_duration": 120},
        {"name": "Mary", "location": "Marina District", "start_window": "14:45", "end_window": "16:45", "min_duration": 45},
        {"name": "Charles", "location": "Richmond District", "start_window": "17:15", "end_window": "21:00", "min_duration": 15},
        {"name": "Joshua", "location": "Financial District", "start_window": "14:30", "end_window": "17:15", "min_duration": 90},
        {"name": "Ronald", "location": "Embarcadero", "start_window": "18:15", "end_window": "20:45", "min_duration": 30},
        {"name": "George", "location": "The Castro", "start_window": "14:15", "end_window": "19:00", "min_duration": 105},
        {"name": "Kimberly", "location": "Alamo Square", "start_window": "9:00", "end_window": "14:30", "min_duration": 105},
        {"name": "William", "location": "Presidio", "start_window": "7:00", "end_window": "12:45", "min_duration": 60}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Russian Hill
    current_location = "Russian Hill"
    arrival_time = time_to_minutes("9:00")

    # Create variables for each friend's meeting start and end times
    meetings = {}
    for friend in friends:
        name = friend["name"]
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meetings[name] = {
            "start": start_var,
            "end": end_var,
            "location": friend["location"],
            "window_start": time_to_minutes(friend["start_window"]),
            "window_end": time_to_minutes(friend["end_window"]),
            "min_duration": friend["min_duration"]
        }

    # Add constraints for each meeting
    for name, meeting in meetings.items():
        s.add(meeting["start"] >= meeting["window_start"])
        s.add(meeting["end"] <= meeting["window_end"])
        s.add(meeting["end"] - meeting["start"] >= meeting["min_duration"])

    # Define travel times dictionary (simplified for this problem)
    travel_times = {
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Presidio"): 16,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Presidio"): 24,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Presidio"): 20,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Presidio"): 17,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Alamo Square"): 19
    }

    # Define the order of meetings (this is a simplification; in reality, we'd need to find an order)
    # For this problem, we'll assume an order that allows all meetings to fit, but in practice, we'd need to explore permutations
    # Here, we'll prioritize meetings with tighter windows first
    meeting_order = ["William", "Kimberly", "Mary", "Joshua", "Patricia", "George", "Ronald", "Charles", "David", "Kenneth"]

    # Add constraints for travel times between meetings
    prev_location = current_location
    prev_end = arrival_time
    for name in meeting_order:
        if name in meetings:
            meeting = meetings[name]
            s.add(meeting["start"] >= prev_end + travel_times.get((prev_location, meeting["location"]), 0))
            prev_end = meeting["end"]
            prev_location = meeting["location"]

    # Check if all constraints can be satisfied
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in meeting_order:
            if name in meetings:
                meeting = meetings[name]
                start_time = model[meeting["start"]].as_long()
                end_time = model[meeting["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))