from z3 import *
import json
from itertools import permutations

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

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

    # Define possible meeting orders (pruned to likely feasible ones)
    possible_orders = [
        ["Joseph", "Rebecca", "Stephanie", "Karen", "Steven", "Brian"],
        ["Joseph", "Rebecca", "Stephanie", "Steven", "Karen", "Brian"],
        ["Rebecca", "Joseph", "Stephanie", "Karen", "Steven", "Brian"],
        ["Joseph", "Rebecca", "Karen", "Stephanie", "Steven", "Brian"],
    ]

    # Try each possible order until we find a feasible schedule
    for order in possible_orders:
        temp_solver = Solver()
        temp_solver.add(s.assertions())

        # Add travel time constraints for this order
        prev_location = "Financial District"
        prev_end = 540  # Starting at 9:00 AM (540 minutes)
        
        for person in order:
            current_loc = friends[person]["location"]
            travel_time = travel_times[(prev_location, current_loc)]
            
            start, end = meeting_vars[person]
            temp_solver.add(start >= prev_end + travel_time)
            
            prev_location = current_loc
            prev_end = end

        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            for name in order:
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

    return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))