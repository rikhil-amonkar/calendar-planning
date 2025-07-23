from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Friends and their details
    friends = {
        "Kenneth": {"location": "Richmond District", "available_start": "21:15", "available_end": "22:00", "min_duration": 30},
        "Lisa": {"location": "Union Square", "available_start": "09:00", "available_end": "16:30", "min_duration": 45},
        "Joshua": {"location": "Financial District", "available_start": "12:00", "available_end": "15:15", "min_duration": 15},
        "Nancy": {"location": "Pacific Heights", "available_start": "08:00", "available_end": "11:30", "min_duration": 90},
        "Andrew": {"location": "Nob Hill", "available_start": "11:30", "available_end": "20:15", "min_duration": 60},
        "John": {"location": "Bayview", "available_start": "16:45", "available_end": "21:30", "min_duration": 75}
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

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {'start': start_var, 'end': end_var}

        # Constraints: meeting duration >= min_duration
        opt.add(end_var - start_var >= friends[name]["min_duration"])

        # Constraints: meeting within friend's availability
        available_start = time_to_minutes(friends[name]["available_start"])
        available_end = time_to_minutes(friends[name]["available_end"])
        opt.add(start_var >= available_start)
        opt.add(end_var <= available_end)

    # Travel times between locations (simplified as symmetric for this example)
    travel_times = {
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Bayview"): 21,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Bayview"): 26,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Bayview"): 15,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Bayview"): 19,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Bayview"): 22,
        ("Nob Hill", "Bayview"): 19,
    }

    # Assume starting at Embarcadero at 9:00 AM (540 minutes)
    current_location = "Embarcadero"
    current_time = 540  # 9:00 AM in minutes

    # Order of meetings (this is a simplification; in reality, we'd need to model the sequence)
    # For simplicity, we'll assume a fixed order based on earliest availability
    meeting_order = ["Nancy", "Lisa", "Joshua", "Andrew", "John", "Kenneth"]

    # Add travel time constraints between consecutive meetings
    for i in range(len(meeting_order) - 1):
        from_person = meeting_order[i]
        to_person = meeting_order[i + 1]
        from_loc = friends[from_person]["location"]
        to_loc = friends[to_person]["location"]
        travel_time = travel_times.get((from_loc, to_loc), travel_times.get((to_loc, from_loc), 0))
        opt.add(meeting_vars[to_person]['start'] >= meeting_vars[from_person]['end'] + travel_time)

    # Ensure the first meeting starts after arriving at Embarcadero
    first_meeting_loc = friends[meeting_order[0]]["location"]
    travel_time = travel_times.get((current_location, first_meeting_loc), travel_times.get((first_meeting_loc, current_location), 0))
    opt.add(meeting_vars[meeting_order[0]]['start'] >= current_time + travel_time)

    # Maximize the total meeting time
    total_meeting_time = Sum([meeting_vars[name]['end'] - meeting_vars[name]['start'] for name in meeting_order])
    opt.maximize(total_meeting_time)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for name in meeting_order:
            start = model.evaluate(meeting_vars[name]['start']).as_long()
            end = model.evaluate(meeting_vars[name]['end']).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))