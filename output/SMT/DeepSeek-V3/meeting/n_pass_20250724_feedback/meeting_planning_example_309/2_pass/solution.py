from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    solver = Solver()

    # Define the friends and their constraints
    friends = [
        {
            "name": "Nancy",
            "location": "Chinatown",
            "available_start": "09:30",
            "available_end": "13:30",
            "min_duration": 90  # minutes
        },
        {
            "name": "Mary",
            "location": "Alamo Square",
            "available_start": "07:00",
            "available_end": "21:00",
            "min_duration": 75  # minutes
        },
        {
            "name": "Jessica",
            "location": "Bayview",
            "available_start": "11:15",
            "available_end": "13:45",
            "min_duration": 45  # minutes
        },
        {
            "name": "Rebecca",
            "location": "Fisherman's Wharf",
            "available_start": "07:00",
            "available_end": "08:30",
            "min_duration": 45  # minutes
        }
    ]

    # Travel times between locations (in minutes)
    travel_times = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Bayview"): 26
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initial time is 9:00 AM (540 minutes)
    initial_time = time_to_minutes("09:00")
    current_location = "Financial District"

    # Create variables for each meeting
    meet_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meet_vars.append((friend, start_var, end_var))

    # Constraints for each meeting
    for friend, start, end in meet_vars:
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        solver.add(start >= available_start)
        solver.add(end <= available_end)
        solver.add(end == start + friend['min_duration'])

    # Try to meet Rebecca first (if possible)
    # Then try to meet others in order of their availability
    possible_orders = [
        ["Rebecca", "Nancy", "Jessica"],
        ["Nancy", "Jessica", "Mary"],
        ["Nancy", "Jessica"],
        ["Nancy", "Mary"],
        ["Nancy"]
    ]

    for order in possible_orders:
        solver.push()
        ordered_friends = []
        for name in order:
            for f in friends:
                if f['name'] == name:
                    ordered_friends.append(f)
                    break

        prev_end = initial_time
        prev_loc = current_location
        for friend in ordered_friends:
            start = Int(f"start_{friend['name']}")
            end = Int(f"end_{friend['name']}")
            travel_time = travel_times.get((prev_loc, friend['location']), 0)
            solver.add(start >= prev_end + travel_time)
            prev_end = end
            prev_loc = friend['location']

        if solver.check() == sat:
            model = solver.model()
            result = []
            for friend in ordered_friends:
                start_val = model.eval(Int(f"start_{friend['name']}")).as_long()
                end_val = start_val + friend['min_duration']
                result.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            return {"itinerary": result}
        else:
            solver.pop()

    return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))