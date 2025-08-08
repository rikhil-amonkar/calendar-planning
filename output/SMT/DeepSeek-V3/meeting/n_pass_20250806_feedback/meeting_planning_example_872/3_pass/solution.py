from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Karen", "location": "Haight-Ashbury", "start": "21:00", "end": "21:45", "duration": 45},
        {"name": "Jessica", "location": "Nob Hill", "start": "13:45", "end": "21:00", "duration": 90},
        {"name": "Brian", "location": "Russian Hill", "start": "15:30", "end": "21:45", "duration": 60},
        {"name": "Kenneth", "location": "North Beach", "start": "09:45", "end": "21:00", "duration": 30},
        {"name": "Jason", "location": "Chinatown", "start": "08:15", "end": "11:45", "duration": 75},
        {"name": "Stephanie", "location": "Union Square", "start": "14:45", "end": "18:45", "duration": 105},
        {"name": "Kimberly", "location": "Embarcadero", "start": "09:45", "end": "19:30", "duration": 75},
        {"name": "Steven", "location": "Financial District", "start": "07:15", "end": "21:15", "duration": 60},
        {"name": "Mark", "location": "Marina District", "start": "10:15", "end": "13:00", "duration": 75}
    ]

    # Travel times dictionary (from_location, to_location) -> minutes
    travel_times = {
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Marina District"): 11,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Marina District"): 12,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Marina District"): 18,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17
    }

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting's start and end times
    meeting_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start_var, end_var))

    # Add constraints for each meeting
    for friend, start, end in meeting_vars:
        friend_start = time_to_minutes(friend["start"])
        friend_end = time_to_minutes(friend["end"])
        s.add(start >= max(friend_start, 540))  # Ensure start is at or after 9:00 AM (540 minutes)
        s.add(end <= friend_end)
        s.add(end == start + friend["duration"])

    # Add travel time constraints between consecutive meetings
    # We'll assume a fixed order for simplicity; a more complete solution would optimize the order
    # Here, we'll enforce that the end time of one meeting + travel time <= start time of the next meeting
    for i in range(len(meeting_vars) - 1):
        current_friend, current_start, current_end = meeting_vars[i]
        next_friend, next_start, next_end = meeting_vars[i + 1]
        travel_time = travel_times.get((current_friend["location"], next_friend["location"]), 0)
        s.add(next_start >= current_end + travel_time)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start, end in meeting_vars:
            start_val = model[start].as_long()
            end_val = model[end].as_long()
            if start_val >= 540:  # Only include meetings starting at or after 9:00 AM
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))