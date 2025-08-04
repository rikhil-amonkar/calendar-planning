from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their details
    friends = {
        "Charles": {"location": "Bayview", "available_start": "11:30", "available_end": "14:30", "min_duration": 45},
        "Robert": {"location": "Sunset District", "available_start": "16:45", "available_end": "21:00", "min_duration": 30},
        "Karen": {"location": "Richmond District", "available_start": "19:15", "available_end": "21:30", "min_duration": 60},
        "Rebecca": {"location": "Nob Hill", "available_start": "16:15", "available_end": "20:30", "min_duration": 90},
        "Margaret": {"location": "Chinatown", "available_start": "14:15", "available_end": "19:45", "min_duration": 120},
        "Patricia": {"location": "Haight-Ashbury", "available_start": "14:30", "available_end": "20:30", "min_duration": 45},
        "Mark": {"location": "North Beach", "available_start": "14:00", "available_end": "18:30", "min_duration": 105},
        "Melissa": {"location": "Russian Hill", "available_start": "13:00", "available_end": "19:45", "min_duration": 30},
        "Laura": {"location": "Embarcadero", "available_start": "07:45", "available_end": "13:15", "min_duration": 105}
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

    # Initialize variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    variables = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        variables[name] = {'start': start_var, 'end': end_var}

        # Available start and end times in minutes
        avail_start = time_to_minutes(friends[name]['available_start'])
        avail_end = time_to_minutes(friends[name]['available_end'])
        min_duration = friends[name]['min_duration']

        # Constraints: meeting must be within available time and duration
        s.add(start_var >= avail_start)
        s.add(end_var <= avail_end)
        s.add(end_var >= start_var + min_duration)

    # Current location starts at Marina District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Marina District"

    # Define travel times (dictionary of dictionaries)
    travel_times = {
        "Marina District": {
            "Bayview": 27,
            "Sunset District": 19,
            "Richmond District": 11,
            "Nob Hill": 12,
            "Chinatown": 15,
            "Haight-Ashbury": 16,
            "North Beach": 11,
            "Russian Hill": 8,
            "Embarcadero": 14
        },
        "Bayview": {
            "Marina District": 27,
            "Sunset District": 23,
            "Richmond District": 25,
            "Nob Hill": 20,
            "Chinatown": 19,
            "Haight-Ashbury": 19,
            "North Beach": 22,
            "Russian Hill": 23,
            "Embarcadero": 19
        },
        "Sunset District": {
            "Marina District": 21,
            "Bayview": 22,
            "Richmond District": 12,
            "Nob Hill": 27,
            "Chinatown": 30,
            "Haight-Ashbury": 15,
            "North Beach": 28,
            "Russian Hill": 24,
            "Embarcadero": 30
        },
        "Richmond District": {
            "Marina District": 9,
            "Bayview": 27,
            "Sunset District": 11,
            "Nob Hill": 17,
            "Chinatown": 20,
            "Haight-Ashbury": 10,
            "North Beach": 17,
            "Russian Hill": 13,
            "Embarcadero": 19
        },
        "Nob Hill": {
            "Marina District": 11,
            "Bayview": 19,
            "Sunset District": 24,
            "Richmond District": 14,
            "Chinatown": 6,
            "Haight-Ashbury": 13,
            "North Beach": 8,
            "Russian Hill": 5,
            "Embarcadero": 9
        },
        "Chinatown": {
            "Marina District": 12,
            "Bayview": 20,
            "Sunset District": 29,
            "Richmond District": 20,
            "Nob Hill": 9,
            "Haight-Ashbury": 19,
            "North Beach": 3,
            "Russian Hill": 7,
            "Embarcadero": 5
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Bayview": 18,
            "Sunset District": 15,
            "Richmond District": 10,
            "Nob Hill": 15,
            "Chinatown": 19,
            "North Beach": 19,
            "Russian Hill": 17,
            "Embarcadero": 20
        },
        "North Beach": {
            "Marina District": 9,
            "Bayview": 25,
            "Sunset District": 27,
            "Richmond District": 18,
            "Nob Hill": 7,
            "Chinatown": 6,
            "Haight-Ashbury": 18,
            "Russian Hill": 4,
            "Embarcadero": 6
        },
        "Russian Hill": {
            "Marina District": 7,
            "Bayview": 23,
            "Sunset District": 23,
            "Richmond District": 14,
            "Nob Hill": 5,
            "Chinatown": 9,
            "Haight-Ashbury": 17,
            "North Beach": 5,
            "Embarcadero": 8
        },
        "Embarcadero": {
            "Marina District": 12,
            "Bayview": 21,
            "Sunset District": 30,
            "Richmond District": 21,
            "Nob Hill": 10,
            "Chinatown": 7,
            "Haight-Ashbury": 21,
            "North Beach": 5,
            "Russian Hill": 8
        }
    }

    # Order of meetings: Laura first (since she's available earliest)
    # Then others in order of their availability start times
    # This is a heuristic to help the solver; actual order is determined by constraints
    meeting_order = ["Laura", "Charles", "Melissa", "Margaret", "Mark", "Patricia", "Rebecca", "Robert", "Karen"]

    # Ensure meetings are scheduled in a feasible order with travel times
    for i in range(len(meeting_order) - 1):
        current_meeting = meeting_order[i]
        next_meeting = meeting_order[i + 1]
        current_loc = friends[current_meeting]["location"]
        next_loc = friends[next_meeting]["location"]
        travel_time = travel_times[current_loc][next_loc]

        s.add(variables[next_meeting]['start'] >= variables[current_meeting]['end'] + travel_time)

    # Also, Laura's meeting must start after arrival at Marina District (9:00 AM) plus travel time to Embarcadero
    s.add(variables["Laura"]['start'] >= 540 + travel_times["Marina District"]["Embarcadero"])

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in meeting_order:
            start = model.evaluate(variables[name]['start']).as_long()
            end = model.evaluate(variables[name]['end']).as_long()
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
solution = solve_scheduling()
print(json.dumps(solution, indent=2))