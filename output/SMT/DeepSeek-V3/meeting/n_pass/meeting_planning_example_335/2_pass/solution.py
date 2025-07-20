from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define the people and their constraints
    people = [
        {"name": "Helen", "location": "North Beach", "start_window": "09:00", "end_window": "17:00", "min_duration": 15},
        {"name": "Betty", "location": "Financial District", "start_window": "19:00", "end_window": "21:45", "min_duration": 90},
        {"name": "Amanda", "location": "Alamo Square", "start_window": "19:45", "end_window": "21:00", "min_duration": 60},
        {"name": "Kevin", "location": "Mission District", "start_window": "10:45", "end_window": "14:45", "min_duration": 45}
    ]

    # Convert time strings to minutes since midnight for easier handling
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Parse time windows to minutes
    for person in people:
        person["start_min"] = time_to_minutes(person["start_window"])
        person["end_min"] = time_to_minutes(person["end_window"])
        person["min_duration_min"] = person["min_duration"]

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Mission District"): 15,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Mission District"): 18,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Mission District"): 17,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Financial District"): 17,
        ("Mission District", "Alamo Square"): 11
    }

    # Current location starts at Pacific Heights at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Pacific Heights"

    # Variables to represent whether each person is met
    meet_vars = {person["name"]: Bool(f"meet_{person['name']}") for person in people}

    # Variables for start and end times of each meeting
    start_times = {person["name"]: Int(f"start_{person['name']}") for person in people}
    end_times = {person["name"]: Int(f"end_{person['name']}") for person in people}

    itinerary = []

    # Constraints for each person
    for person in people:
        name = person["name"]
        opt.add(Implies(meet_vars[name], start_times[name] >= person["start_min"]))
        opt.add(Implies(meet_vars[name], end_times[name] <= person["end_min"]))
        opt.add(Implies(meet_vars[name], end_times[name] == start_times[name] + person["min_duration_min"]))
        opt.add(Implies(Not(meet_vars[name]), start_times[name] == -1))
        opt.add(Implies(Not(meet_vars[name]), end_times[name] == -1))

    # Constraints for ordering meetings and travel times
    # We'll try to meet Kevin first, then Helen, then Amanda, then Betty
    # This is based on their time windows

    # Start at Pacific Heights at 9:00 AM (540 minutes)
    prev_end = current_time
    prev_location = current_location

    # Try to meet Kevin first
    kevin = next(p for p in people if p["name"] == "Kevin")
    travel_time = travel_times[(prev_location, kevin["location"])]
    opt.add(Implies(meet_vars["Kevin"], start_times["Kevin"] >= prev_end + travel_time))
    opt.add(Implies(meet_vars["Kevin"], end_times["Kevin"] == start_times["Kevin"] + kevin["min_duration_min"]))
    opt.add(Implies(meet_vars["Kevin"], start_times["Kevin"] >= kevin["start_min"]))
    opt.add(Implies(meet_vars["Kevin"], end_times["Kevin"] <= kevin["end_min"]))

    # After Kevin, try to meet Helen
    helen = next(p for p in people if p["name"] == "Helen")
    travel_time_kevin_helen = travel_times[(kevin["location"], helen["location"])]
    opt.add(Implies(And(meet_vars["Kevin"], meet_vars["Helen"]), start_times["Helen"] >= end_times["Kevin"] + travel_time_kevin_helen))
    opt.add(Implies(meet_vars["Helen"], end_times["Helen"] == start_times["Helen"] + helen["min_duration_min"]))
    opt.add(Implies(meet_vars["Helen"], start_times["Helen"] >= helen["start_min"]))
    opt.add(Implies(meet_vars["Helen"], end_times["Helen"] <= helen["end_min"]))

    # After Helen, try to meet Amanda
    amanda = next(p for p in people if p["name"] == "Amanda")
    travel_time_helen_amanda = travel_times[(helen["location"], amanda["location"])]
    opt.add(Implies(And(meet_vars["Helen"], meet_vars["Amanda"]), start_times["Amanda"] >= end_times["Helen"] + travel_time_helen_amanda))
    opt.add(Implies(meet_vars["Amanda"], end_times["Amanda"] == start_times["Amanda"] + amanda["min_duration_min"]))
    opt.add(Implies(meet_vars["Amanda"], start_times["Amanda"] >= amanda["start_min"]))
    opt.add(Implies(meet_vars["Amanda"], end_times["Amanda"] <= amanda["end_min"]))

    # After Amanda, try to meet Betty
    betty = next(p for p in people if p["name"] == "Betty")
    travel_time_amanda_betty = travel_times[(amanda["location"], betty["location"])]
    opt.add(Implies(And(meet_vars["Amanda"], meet_vars["Betty"]), start_times["Betty"] >= end_times["Amanda"] + travel_time_amanda_betty))
    opt.add(Implies(meet_vars["Betty"], end_times["Betty"] == start_times["Betty"] + betty["min_duration_min"]))
    opt.add(Implies(meet_vars["Betty"], start_times["Betty"] >= betty["start_min"]))
    opt.add(Implies(meet_vars["Betty"], end_times["Betty"] <= betty["end_min"]))

    # Maximize the number of people met
    opt.maximize(Sum([If(meet_vars[p["name"]], 1, 0) for p in people]))

    # Check if the optimizer can find a solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for person in people:
            name = person["name"]
            if is_true(model[meet_vars[name]]):
                start = model[start_times[name]].as_long()
                end = model[end_times[name]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))