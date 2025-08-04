from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Richard": {"location": "Embarcadero", "available_start": "15:15", "available_end": "18:45", "min_duration": 90},
        "Mark": {"location": "Pacific Heights", "available_start": "15:00", "available_end": "17:00", "min_duration": 45},
        "Matthew": {"location": "Russian Hill", "available_start": "17:30", "available_end": "21:00", "min_duration": 90},
        "Rebecca": {"location": "Haight-Ashbury", "available_start": "14:45", "available_end": "18:00", "min_duration": 60},
        "Melissa": {"location": "Golden Gate Park", "available_start": "13:45", "available_end": "17:30", "min_duration": 90},
        "Margaret": {"location": "Fisherman's Wharf", "available_start": "14:45", "available_end": "20:15", "min_duration": 15},
        "Emily": {"location": "Sunset District", "available_start": "15:45", "available_end": "17:00", "min_duration": 45},
        "George": {"location": "The Castro", "available_start": "14:00", "available_end": "16:15", "min_duration": 75}
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Chinatown": {
            "Embarcadero": 5,
            "Pacific Heights": 10,
            "Russian Hill": 7,
            "Haight-Ashbury": 19,
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 8,
            "Sunset District": 29,
            "The Castro": 22
        },
        "Embarcadero": {
            "Chinatown": 7,
            "Pacific Heights": 11,
            "Russian Hill": 8,
            "Haight-Ashbury": 21,
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Sunset District": 30,
            "The Castro": 25
        },
        "Pacific Heights": {
            "Chinatown": 11,
            "Embarcadero": 10,
            "Russian Hill": 7,
            "Haight-Ashbury": 11,
            "Golden Gate Park": 15,
            "Fisherman's Wharf": 13,
            "Sunset District": 21,
            "The Castro": 16
        },
        "Russian Hill": {
            "Chinatown": 9,
            "Embarcadero": 8,
            "Pacific Heights": 7,
            "Haight-Ashbury": 17,
            "Golden Gate Park": 21,
            "Fisherman's Wharf": 7,
            "Sunset District": 23,
            "The Castro": 21
        },
        "Haight-Ashbury": {
            "Chinatown": 19,
            "Embarcadero": 20,
            "Pacific Heights": 12,
            "Russian Hill": 17,
            "Golden Gate Park": 7,
            "Fisherman's Wharf": 23,
            "Sunset District": 15,
            "The Castro": 6
        },
        "Golden Gate Park": {
            "Chinatown": 23,
            "Embarcadero": 25,
            "Pacific Heights": 16,
            "Russian Hill": 19,
            "Haight-Ashbury": 7,
            "Fisherman's Wharf": 24,
            "Sunset District": 10,
            "The Castro": 13
        },
        "Fisherman's Wharf": {
            "Chinatown": 12,
            "Embarcadero": 8,
            "Pacific Heights": 12,
            "Russian Hill": 7,
            "Haight-Ashbury": 22,
            "Golden Gate Park": 25,
            "Sunset District": 27,
            "The Castro": 27
        },
        "Sunset District": {
            "Chinatown": 30,
            "Embarcadero": 30,
            "Pacific Heights": 21,
            "Russian Hill": 24,
            "Haight-Ashbury": 15,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 29,
            "The Castro": 17
        },
        "The Castro": {
            "Chinatown": 22,
            "Embarcadero": 22,
            "Pacific Heights": 16,
            "Russian Hill": 18,
            "Haight-Ashbury": 6,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 24,
            "Sunset District": 17
        }
    }

    # Create Z3 variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = {"start": start, "end": end}

    # Add constraints for each meeting
    for name, data in friends.items():
        available_start = time_to_minutes(data["available_start"])
        available_end = time_to_minutes(data["available_end"])
        min_duration = data["min_duration"]

        s.add(meeting_vars[name]["start"] >= available_start)
        s.add(meeting_vars[name]["end"] <= available_end)
        s.add(meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration)

    # Add constraints for travel times between consecutive meetings
    # We need to ensure that the start time of the next meeting is after the end time of the previous meeting plus travel time
    # To simplify, we'll assume a fixed order of meetings and add constraints accordingly
    # However, in reality, the order is part of the optimization problem
    # For this problem, we'll use a heuristic to prioritize meetings with tighter windows first

    # Define a heuristic order based on available time windows
    order = ["George", "Melissa", "Margaret", "Rebecca", "Mark", "Richard", "Emily", "Matthew"]

    # Add travel time constraints between consecutive meetings in the order
    for i in range(len(order) - 1):
        current = order[i]
        next_person = order[i + 1]
        current_loc = friends[current]["location"]
        next_loc = friends[next_person]["location"]
        travel_time = travel_times[current_loc][next_loc]
        s.add(meeting_vars[next_person]["start"] >= meeting_vars[current]["end"] + travel_time)

    # Ensure all meetings are scheduled
    for name in friends:
        s.add(meeting_vars[name]["start"] >= 0)
        s.add(meeting_vars[name]["end"] >= 0)

    # Try to maximize the number of meetings (all in this case)
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start_time = model[meeting_vars[name]["start"]].as_long()
            end_time = model[meeting_vars[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))