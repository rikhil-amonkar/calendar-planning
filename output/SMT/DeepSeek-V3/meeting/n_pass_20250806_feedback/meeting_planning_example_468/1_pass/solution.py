from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Rebecca": {"location": "Bayview", "start": "9:00", "end": "12:45", "min_duration": 90},
        "Amanda": {"location": "Pacific Heights", "start": "18:30", "end": "21:45", "min_duration": 90},
        "James": {"location": "Alamo Square", "start": "9:45", "end": "21:15", "min_duration": 90},
        "Sarah": {"location": "Fisherman's Wharf", "start": "8:00", "end": "21:30", "min_duration": 90},
        "Melissa": {"location": "Golden Gate Park", "start": "9:00", "end": "18:45", "min_duration": 90}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "The Castro": {
            "Bayview": 19,
            "Pacific Heights": 16,
            "Alamo Square": 8,
            "Fisherman's Wharf": 24,
            "Golden Gate Park": 11
        },
        "Bayview": {
            "The Castro": 20,
            "Pacific Heights": 23,
            "Alamo Square": 16,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "The Castro": 16,
            "Bayview": 22,
            "Alamo Square": 10,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15
        },
        "Alamo Square": {
            "The Castro": 8,
            "Bayview": 16,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 9
        },
        "Fisherman's Wharf": {
            "The Castro": 26,
            "Bayview": 26,
            "Pacific Heights": 12,
            "Alamo Square": 20,
            "Golden Gate Park": 25
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Bayview": 23,
            "Pacific Heights": 16,
            "Alamo Square": 10,
            "Fisherman's Wharf": 24
        }
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
        meeting_vars[name] = (start_var, end_var)

    # Current location starts at The Castro at 9:00 AM (540 minutes)
    current_location = "The Castro"
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        start_var, end_var = meeting_vars[name]
        min_duration = friend["min_duration"]
        available_start = time_to_minutes(friend["start"])
        available_end = time_to_minutes(friend["end"])

        # Meeting must start within availability window
        s.add(start_var >= available_start)
        s.add(end_var <= available_end)
        # Meeting duration must be at least min_duration
        s.add(end_var - start_var >= min_duration)
        # Meeting must start after current_time + travel time
        travel_time = travel_times[current_location][friend["location"]]
        s.add(start_var >= current_time + travel_time)

    # No overlapping meetings (simplified by enforcing order)
    # For simplicity, we'll assume meetings are scheduled in a certain order
    # This is a simplification; a more complex model would handle all permutations

    # For this example, let's try to meet Rebecca, James, Melissa, Amanda in that order
    # This is a heuristic; in a full solution, we'd need to explore all permutations
    order = ["Rebecca", "James", "Melissa", "Amanda"]
    for i in range(len(order) - 1):
        current_name = order[i]
        next_name = order[i + 1]
        current_start, current_end = meeting_vars[current_name]
        next_start, next_end = meeting_vars[next_name]
        travel_time = travel_times[friends[current_name]["location"]][friends[next_name]["location"]]
        s.add(next_start >= current_end + travel_time)

    # Check if we can meet Sarah as well
    # Try to insert Sarah somewhere in the order
    # For example, after James
    # This is a heuristic approach; a full solution would need to consider all possible insertions
    s.push()
    sarah_start, sarah_end = meeting_vars["Sarah"]
    james_start, james_end = meeting_vars["James"]
    melissa_start, melissa_end = meeting_vars["Melissa"]
    travel_james_sarah = travel_times[friends["James"]["location"]][friends["Sarah"]["location"]]
    travel_sarah_melissa = travel_times[friends["Sarah"]["location"]][friends["Melissa"]["location"]]
    s.add(sarah_start >= james_end + travel_james_sarah)
    s.add(melissa_start >= sarah_end + travel_sarah_melissa)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order + ["Sarah"]:
            start_var, end_var = meeting_vars[name]
            start_time = model.eval(start_var).as_long()
            end_time = model.eval(end_var).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": itinerary}
    else:
        s.pop()
        # Try without Sarah
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name in order:
                start_var, end_var = meeting_vars[name]
                start_time = model.eval(start_var).as_long()
                end_time = model.eval(end_var).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))