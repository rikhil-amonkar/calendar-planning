from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the friends and their details
    friends = {
        "Karen": {
            "location": "Haight-Ashbury",
            "available_start": "21:00",
            "available_end": "21:45",
            "duration": 45
        },
        "Jessica": {
            "location": "Nob Hill",
            "available_start": "13:45",
            "available_end": "21:00",
            "duration": 90
        },
        "Brian": {
            "location": "Russian Hill",
            "available_start": "15:30",
            "available_end": "21:45",
            "duration": 60
        },
        "Kenneth": {
            "location": "North Beach",
            "available_start": "09:45",
            "available_end": "21:00",
            "duration": 30
        },
        "Jason": {
            "location": "Chinatown",
            "available_start": "08:15",
            "available_end": "11:45",
            "duration": 75
        },
        "Stephanie": {
            "location": "Union Square",
            "available_start": "14:45",
            "available_end": "18:45",
            "duration": 105
        },
        "Kimberly": {
            "location": "Embarcadero",
            "available_start": "09:45",
            "available_end": "19:30",
            "duration": 75
        },
        "Steven": {
            "location": "Financial District",
            "available_start": "07:15",
            "available_end": "21:15",
            "duration": 60
        },
        "Mark": {
            "location": "Marina District",
            "available_start": "10:15",
            "available_end": "13:00",
            "duration": 75
        }
    }

    # Define travel times (simplified for this example)
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
        ("Marina District", "Financial District"): 17,
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

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_location = "Presidio"
    current_time = 540  # 9:00 AM in minutes

    itinerary = []

    # Try to meet as many friends as possible in order
    for friend, details in friends.items():
        location = details["location"]
        available_start = time_to_minutes(details["available_start"])
        available_end = time_to_minutes(details["available_end"])
        duration = details["duration"]

        # Calculate travel time from current location to friend's location
        travel_time = travel_times.get((current_location, location), 0)

        # Earliest possible start time is max of current_time + travel_time and friend's available_start
        earliest_start = max(current_time + travel_time, available_start)

        # Latest possible start time is friend's available_end - duration
        latest_start = available_end - duration

        if earliest_start <= latest_start:
            # Schedule the meeting
            start_time = earliest_start
            end_time = start_time + duration

            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })

            # Update current location and time
            current_location = location
            current_time = end_time

    return {"itinerary": itinerary}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))