from z3 import *
import json

def solve_scheduling_problem():
    solver = Optimize()

    friends = {
        "Jeffrey": {"location": "Fisherman's Wharf", "available_start": "10:15", "available_end": "13:00", "min_duration": 90},
        "Ronald": {"location": "Alamo Square", "available_start": "7:45", "available_end": "14:45", "min_duration": 120},
        "Jason": {"location": "Financial District", "available_start": "10:45", "available_end": "16:00", "min_duration": 105},
        "Melissa": {"location": "Union Square", "available_start": "17:45", "available_end": "18:15", "min_duration": 15},
        "Elizabeth": {"location": "Sunset District", "available_start": "14:45", "available_end": "17:30", "min_duration": 105},
        "Margaret": {"location": "Embarcadero", "available_start": "13:15", "available_end": "19:00", "min_duration": 90},
        "George": {"location": "Golden Gate Park", "available_start": "19:00", "available_end": "22:00", "min_duration": 75},
        "Richard": {"location": "Chinatown", "available_start": "9:30", "available_end": "21:00", "min_duration": 15},
        "Laura": {"location": "Richmond District", "available_start": "9:45", "available_end": "18:00", "min_duration": 60}
    }

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    travel_times = {
        "Presidio": {
            "Fisherman's Wharf": 19, "Alamo Square": 19, "Financial District": 23,
            "Union Square": 22, "Sunset District": 15, "Embarcadero": 20,
            "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
        },
        # ... (other travel times remain the same as before)
    }

    # Create variables for each friend's meeting
    meet_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meet_vars[name] = (start_var, end_var)

    # Constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        start_var, end_var = meet_vars[name]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        solver.add(start_var >= available_start)
        solver.add(end_var <= available_end)
        solver.add(end_var >= start_var + min_duration)

    # Additional constraints to ensure we start at Presidio at 9:00 AM
    # and account for travel time to first meeting
    first_meeting = True
    for name in friends:
        friend = friends[name]
        start_var, end_var = meet_vars[name]
        travel_time = travel_times["Presidio"][friend["location"]]
        
        if first_meeting:
            # First meeting must start after travel time from Presidio
            solver.add(start_var >= 540 + travel_time)  # 9:00 AM + travel time
            first_meeting = False
        else:
            # For other meetings, ensure they don't overlap with first meeting
            solver.add(Or(
                end_var <= 540 + travel_time,  # Ends before first meeting starts
                start_var >= meet_vars[first_meeting_name][1] + travel_time  # Starts after first meeting ends + travel
            ))

    # Track which friends are met
    met = {name: Bool(f'met_{name}') for name in friends}
    for name in friends:
        start_var, end_var = meet_vars[name]
        solver.add(Implies(met[name], start_var >= 0))
        solver.add(Implies(Not(met[name]), start_var == -1))

    # Maximize number of friends met
    solver.maximize(Sum([If(met[name], 1, 0) for name in friends]))

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in friends:
            if is_true(model[met[name]]):
                start_time = model[meet_vars[name][0]].as_long()
                end_time = model[meet_vars[name][1]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))