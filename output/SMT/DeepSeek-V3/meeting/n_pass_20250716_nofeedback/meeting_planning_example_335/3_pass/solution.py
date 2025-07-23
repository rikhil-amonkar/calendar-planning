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

    # Variables to represent the order of meetings
    # We'll use a list to represent the sequence of meetings
    sequence = [Int(f"seq_{i}") for i in range(len(people))]

    # Each sequence variable should be a unique index representing a person
    opt.add(Distinct(sequence))
    for i in range(len(people)):
        opt.add(sequence[i] >= 0)
        opt.add(sequence[i] < len(people))

    # Constraints for each person
    for person in people:
        name = person["name"]
        opt.add(Implies(meet_vars[name], start_times[name] >= person["start_min"]))
        opt.add(Implies(meet_vars[name], end_times[name] <= person["end_min"]))
        opt.add(Implies(meet_vars[name], end_times[name] == start_times[name] + person["min_duration_min"]))
        opt.add(Implies(Not(meet_vars[name]), start_times[name] == -1))
        opt.add(Implies(Not(meet_vars[name]), end_times[name] == -1))

    # Constraints for ordering meetings and travel times
    # We'll enforce that the start time of a meeting is after the end time of the previous meeting plus travel time
    for i in range(1, len(people)):
        prev_person = people[sequence[i-1]]
        curr_person = people[sequence[i]]
        travel_time = travel_times[(prev_person["location"], curr_person["location"])]
        opt.add(Implies(And(meet_vars[prev_person["name"]], meet_vars[curr_person["name"]]),
                      start_times[curr_person["name"]] >= end_times[prev_person["name"]] + travel_time))

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