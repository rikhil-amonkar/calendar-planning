from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define the friends and their details
    friends = [
        {"name": "Matthew", "location": "The Castro", "available_start": "16:30", "available_end": "20:00", "min_duration": 45},
        {"name": "Rebecca", "location": "Nob Hill", "available_start": "15:15", "available_end": "19:15", "min_duration": 105},
        {"name": "Brian", "location": "Marina District", "available_start": "14:15", "available_end": "22:00", "min_duration": 30},
        {"name": "Emily", "location": "Pacific Heights", "available_start": "11:15", "available_end": "19:45", "min_duration": 15},
        {"name": "Karen", "location": "Haight-Ashbury", "available_start": "11:45", "available_end": "17:30", "min_duration": 30},
        {"name": "Stephanie", "location": "Mission District", "available_start": "13:00", "available_end": "15:45", "min_duration": 75},
        {"name": "James", "location": "Chinatown", "available_start": "14:30", "available_end": "19:00", "min_duration": 120},
        {"name": "Steven", "location": "Russian Hill", "available_start": "14:00", "available_end": "20:00", "min_duration": 30},
        {"name": "Elizabeth", "location": "Alamo Square", "available_start": "13:00", "available_end": "17:15", "min_duration": 120},
        {"name": "William", "location": "Bayview", "available_start": "18:15", "available_end": "20:15", "min_duration": 90}
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

    # Initialize variables for each friend's meeting start and end times
    meeting_starts = {}
    meeting_ends = {}
    for friend in friends:
        name = friend["name"]
        meeting_starts[name] = Int(f'start_{name}')
        meeting_ends[name] = Int(f'end_{name}')

    # Add constraints for each friend's meeting time
    for friend in friends:
        name = friend["name"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        s.add(meeting_starts[name] >= available_start)
        s.add(meeting_ends[name] <= available_end)
        s.add(meeting_ends[name] == meeting_starts[name] + min_duration)

    # Define travel times between locations
    travel_times = {
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Bayview"): 27,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Bayview"): 22,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Bayview"): 14,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Bayview"): 20,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "The Castro"): 18,
        ("Russian Hill", "Bayview"): 23,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "The Castro"): 16,
        ("Nob Hill", "Bayview"): 19,
        ("Marina District", "The Castro"): 21,
        ("Marina District", "Bayview"): 27,
        ("The Castro", "Bayview"): 19
    }

    # Create a sequence variable to represent the order of meetings
    num_friends = len(friends)
    sequence = [Int(f'seq_{i}') for i in range(num_friends)]
    s.add(Distinct(sequence))
    for i in range(num_friends):
        s.add(sequence[i] >= 0)
        s.add(sequence[i] < num_friends)

    # Add travel time constraints between consecutive meetings
    for i in range(num_friends - 1):
        current_idx = sequence[i]
        next_idx = sequence[i + 1]
        
        # Get current and next friend
        current_friend = friends[current_idx]
        next_friend = friends[next_idx]
        
        # Get locations
        current_loc = current_friend["location"]
        next_loc = next_friend["location"]
        
        # Add travel time constraint
        s.add(meeting_starts[next_friend["name"]] >= meeting_ends[current_friend["name"]] + travel_times[(current_loc, next_loc)])

    # First meeting must be reachable from Richmond District
    first_idx = sequence[0]
    first_friend = friends[first_idx]
    first_loc = first_friend["location"]
    s.add(meeting_starts[first_friend["name"]] >= 540 + travel_times[("Richmond District", first_loc)])

    # Last meeting must allow reaching Bayview if William is last
    last_idx = sequence[-1]
    last_friend = friends[last_idx]
    if last_friend["name"] == "William":
        last_loc = last_friend["location"]
        s.add(meeting_ends["William"] + travel_times[(last_loc, "Bayview")] <= time_to_minutes("20:15"))

    # Try to maximize the number of friends met
    met = [If(meeting_starts[f["name"]] >= 0, 1, 0) for f in friends]
    s.maximize(Sum(met))

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Get the meeting order from the sequence
        meeting_order = sorted([(model.evaluate(sequence[i]).as_long(), i) for i in range(num_friends)], key=lambda x: x[1])
        meeting_order = [friends[idx] for idx, pos in meeting_order]
        
        for friend in meeting_order:
            name = friend["name"]
            start = model.evaluate(meeting_starts[name]).as_long()
            end = model.evaluate(meeting_ends[name]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the scheduling problem
solution = solve_scheduling()
print(json.dumps(solution, indent=2))