from z3 import *
import json
from itertools import permutations

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define the friends and their constraints
    friends = {
        "Stephanie": {
            "location": "Golden Gate Park",
            "available_start": "11:00",
            "available_end": "15:00",
            "min_duration": 105,
        },
        "Karen": {
            "location": "Chinatown",
            "available_start": "13:45",
            "available_end": "16:30",
            "min_duration": 15,
        },
        "Brian": {
            "location": "Union Square",
            "available_start": "15:00",
            "available_end": "17:15",
            "min_duration": 30,
        },
        "Rebecca": {
            "location": "Fisherman's Wharf",
            "available_start": "08:00",
            "available_end": "11:15",
            "min_duration": 30,
        },
        "Joseph": {
            "location": "Pacific Heights",
            "available_start": "08:15",
            "available_end": "09:30",
            "min_duration": 60,
        },
        "Steven": {
            "location": "North Beach",
            "available_start": "14:30",
            "available_end": "20:45",
            "min_duration": 120,
        }
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

    # Travel times dictionary
    travel_times = {
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "North Beach"): 7,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "North Beach"): 3,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "North Beach"): 10,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "North Beach"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,
    }

    # Create Z3 variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = (start, end)
        s.add(start >= 0, end >= 0)

    # Add constraints for each friend's meeting
    for name, info in friends.items():
        start, end = meeting_vars[name]
        available_start = time_to_minutes(info["available_start"])
        available_end = time_to_minutes(info["available_end"])
        min_duration = info["min_duration"]

        # Meeting must start and end within the friend's availability
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end - start >= min_duration)

    # Create variables to represent the meeting order
    n = len(friends)
    order = [Int(f"order_{i}") for i in range(n)]
    s.add(Distinct(order))
    s.add([And(o >= 0, o < n) for o in order])

    # Create a mapping from order position to friend name
    friend_names = list(friends.keys())
    position_to_friend = {i: name for i, name in enumerate(friend_names)}

    # Add travel time constraints based on order
    for i in range(n - 1):
        current_pos = order[i]
        next_pos = order[i + 1]
        
        current_friend = position_to_friend[current_pos]
        next_friend = position_to_friend[next_pos]
        
        current_loc = friends[current_friend]["location"]
        next_loc = friends[next_friend]["location"]
        travel_time = travel_times[(current_loc, next_loc)]
        
        current_end = meeting_vars[current_friend][1]
        next_start = meeting_vars[next_friend][0]
        s.add(next_start >= current_end + travel_time)

    # Add constraint for first meeting (must start after arrival at Financial District)
    first_friend = position_to_friend[order[0]]
    first_loc = friends[first_friend]["location"]
    travel_to_first = travel_times[("Financial District", first_loc)]
    first_start = meeting_vars[first_friend][0]
    s.add(first_start >= 540 + travel_to_first)  # 9:00 AM is 540 minutes

    # Maximize the number of meetings (though we want all in this case)
    meeting_flags = [Bool(f"meet_{name}") for name in friends]
    for name, flag in zip(friends, meeting_flags):
        start, end = meeting_vars[name]
        s.add(flag == (end > start))
    s.maximize(Sum([If(flag, 1, 0) for flag in meeting_flags]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Get the order of meetings
        meeting_order = []
        for i in range(n):
            pos = model.eval(order[i]).as_long()
            meeting_order.append((pos, friend_names[pos]))
        
        # Sort by position
        meeting_order.sort()
        itinerary = []
        for pos, name in meeting_order:
            start, end = meeting_vars[name]
            start_time = model.eval(start).as_long()
            end_time = model.eval(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time),
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))