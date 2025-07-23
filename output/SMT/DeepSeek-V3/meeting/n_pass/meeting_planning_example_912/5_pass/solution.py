from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints
    friends = [
        {"name": "Kimberly", "location": "Presidio", "start": "15:30", "end": "16:00", "min_duration": 15},
        {"name": "Elizabeth", "location": "Alamo Square", "start": "19:15", "end": "20:15", "min_duration": 15},
        {"name": "Joshua", "location": "Marina District", "start": "10:30", "end": "14:15", "min_duration": 45},
        {"name": "Sandra", "location": "Financial District", "start": "19:30", "end": "20:15", "min_duration": 45},
        {"name": "Kenneth", "location": "Nob Hill", "start": "12:45", "end": "21:45", "min_duration": 30},
        {"name": "Betty", "location": "Sunset District", "start": "14:00", "end": "19:00", "min_duration": 60},
        {"name": "Deborah", "location": "Chinatown", "start": "17:15", "end": "20:30", "min_duration": 15},
        {"name": "Barbara", "location": "Russian Hill", "start": "17:30", "end": "21:15", "min_duration": 120},
        {"name": "Steven", "location": "North Beach", "start": "17:45", "end": "20:45", "min_duration": 90},
        {"name": "Daniel", "location": "Haight-Ashbury", "start": "18:30", "end": "18:45", "min_duration": 15}
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

    # Travel times dictionary
    travel_times = {
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19
    }

    # Create variables for each friend's meeting start and end times
    meeting_starts = {}
    meeting_ends = {}
    for friend in friends:
        name = friend["name"]
        meeting_starts[name] = Int(f'start_{name}')
        meeting_ends[name] = Int(f'end_{name}')

    # Current location starts at Union Square at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Union Square"

    # Constraints for each friend
    for friend in friends:
        name = friend["name"]
        location = friend["location"]
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        # Meeting must start within window
        s.add(meeting_starts[name] >= start_window)
        s.add(meeting_ends[name] <= end_window)
        # Meeting duration must be at least min_duration
        s.add(meeting_ends[name] >= meeting_starts[name] + min_duration)

    # Define the order of meetings (simplified for this example)
    # We'll prioritize friends with tighter windows or longer required durations
    # This is a heuristic; the actual order may vary
    meeting_order = ["Joshua", "Kenneth", "Betty", "Kimberly", "Deborah", "Barbara", "Steven", "Daniel", "Elizabeth", "Sandra"]

    # Add travel time constraints between consecutive meetings
    for i in range(len(meeting_order) - 1):
        current_friend = meeting_order[i]
        next_friend = meeting_order[i + 1]
        current_loc = next((f["location"] for f in friends if f["name"] == current_friend), "Union Square")
        next_loc = next((f["location"] for f in friends if f["name"] == next_friend), "Union Square")
        travel_time = travel_times.get((current_loc, next_loc), 0)
        s.add(meeting_starts[next_friend] >= meeting_ends[current_friend] + travel_time)

    # Ensure no overlapping meetings
    for i in range(len(meeting_order)):
        for j in range(i + 1, len(meeting_order)):
            f1 = meeting_order[i]
            f2 = meeting_order[j]
            s.add(Or(
                meeting_ends[f1] <= meeting_starts[f2],
                meeting_ends[f2] <= meeting_starts[f1]
            ))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            start = m[meeting_starts[name]].as_long()
            end = m[meeting_ends[name]].as_long()
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