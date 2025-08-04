from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their details
    friends = [
        {"name": "Paul", "location": "Nob Hill", "start": "16:15", "end": "21:15", "min_duration": 60},
        {"name": "Carol", "location": "Union Square", "start": "18:00", "end": "20:15", "min_duration": 120},
        {"name": "Patricia", "location": "Chinatown", "start": "20:00", "end": "21:30", "min_duration": 75},
        {"name": "Karen", "location": "The Castro", "start": "17:00", "end": "19:00", "min_duration": 45},
        {"name": "Nancy", "location": "Presidio", "start": "11:45", "end": "22:00", "min_duration": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "start": "20:00", "end": "20:45", "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "start": "15:45", "end": "21:45", "min_duration": 75}
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

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Bayview": {
            "Nob Hill": 20,
            "Union Square": 17,
            "Chinatown": 18,
            "The Castro": 20,
            "Presidio": 31,
            "Pacific Heights": 23,
            "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19,
            "Union Square": 7,
            "Chinatown": 6,
            "The Castro": 17,
            "Presidio": 17,
            "Pacific Heights": 8,
            "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15,
            "Nob Hill": 9,
            "Chinatown": 7,
            "The Castro": 19,
            "Presidio": 24,
            "Pacific Heights": 15,
            "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 7,
            "The Castro": 22,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19,
            "Nob Hill": 16,
            "Union Square": 19,
            "Chinatown": 20,
            "Presidio": 20,
            "Pacific Heights": 16,
            "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31,
            "Nob Hill": 18,
            "Union Square": 22,
            "Chinatown": 21,
            "The Castro": 21,
            "Pacific Heights": 11,
            "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 12,
            "Chinatown": 11,
            "The Castro": 16,
            "Presidio": 11,
            "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23,
            "Nob Hill": 5,
            "Union Square": 11,
            "Chinatown": 9,
            "The Castro": 21,
            "Presidio": 14,
            "Pacific Heights": 7
        }
    }

    # Create Z3 variables for each friend's meeting start and end times
    meeting_starts = {}
    meeting_ends = {}
    for friend in friends:
        name = friend["name"]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        # Create Z3 integer variables for start and end times
        meeting_starts[name] = Int(f"start_{name}")
        meeting_ends[name] = Int(f"end_{name}")
        # Constrain start and end times to be within the friend's availability
        s.add(meeting_starts[name] >= start_min)
        s.add(meeting_ends[name] <= end_min)
        # Constrain meeting duration to be at least the minimum required
        s.add(meeting_ends[name] - meeting_starts[name] >= friend["min_duration"])

    # Current location starts at Bayview at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Bayview"

    # To model the order of meetings, we'll use a list of booleans indicating whether a meeting is scheduled before another
    # For simplicity, we'll assume a specific order and add constraints accordingly
    # Alternatively, we can use a more complex model with sequencing variables, but for brevity, we'll proceed with a heuristic order

    # Define a possible order of meetings based on their time windows
    # This is a heuristic; the solver will adjust timings to fit constraints
    ordered_friends = sorted(friends, key=lambda x: time_to_minutes(x["start"]))

    # Iterate through the ordered friends and add travel time constraints
    for i in range(len(ordered_friends)):
        friend = ordered_friends[i]
        name = friend["name"]
        location = friend["location"]
        # Travel time from current location to friend's location
        travel_time = travel_times[current_location][location]
        # The meeting can start only after current_time + travel_time
        s.add(meeting_starts[name] >= current_time + travel_time)
        # Update current_time and current_location to this meeting's end
        current_time = meeting_ends[name]
        current_location = location

    # Also, ensure no overlapping meetings (simplified by the order)
    for i in range(len(ordered_friends) - 1):
        friend1 = ordered_friends[i]
        friend2 = ordered_friends[i + 1]
        s.add(meeting_ends[friend1["name"]] + travel_times[friend1["location"]][friend2["location"]] <= meeting_starts[friend2["name"]])

    # Maximize the number of friends met (or total meeting time)
    # Here, we'll maximize the total meeting time
    total_meeting_time = sum([meeting_ends[friend["name"]] - meeting_starts[friend["name"]] for friend in friends])
    s.maximize(total_meeting_time)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            start = model.eval(meeting_starts[name]).as_long()
            end = model.eval(meeting_ends[name]).as_long()
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

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))