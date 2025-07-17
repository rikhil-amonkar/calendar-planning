from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the districts and their indices
    districts = {
        "Richmond District": 0,
        "Marina District": 1,
        "Chinatown": 2,
        "Financial District": 3,
        "Bayview": 4,
        "Union Square": 5
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 9, 20, 22, 26, 21],   # Richmond District
        [11, 0, 16, 17, 27, 16],   # Marina District
        [20, 12, 0, 5, 22, 7],     # Chinatown
        [21, 15, 5, 0, 19, 9],     # Financial District
        [25, 25, 18, 19, 0, 17],   # Bayview
        [20, 18, 7, 9, 15, 0]      # Union Square
    ]

    # Friends' data
    friends = [
        {"name": "Kimberly", "district": "Marina District", "start": 13.25, "end": 16.75, "min_duration": 0.25},
        {"name": "Robert", "district": "Chinatown", "start": 12.25, "end": 20.25, "min_duration": 0.25},
        {"name": "Rebecca", "district": "Financial District", "start": 13.25, "end": 16.75, "min_duration": 1.25},
        {"name": "Margaret", "district": "Bayview", "start": 9.5, "end": 13.5, "min_duration": 0.5},
        {"name": "Kenneth", "district": "Union Square", "start": 19.5, "end": 21.25, "min_duration": 1.25}
    ]

    # Convert start and end times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_float):
        hours = int(time_float)
        minutes = int((time_float - hours) * 60)
        return hours * 60 + minutes - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Variables for each meeting's start and end times (in minutes since 9:00 AM)
    meet_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        availability_start = time_to_minutes(friend["start"])
        availability_end = time_to_minutes(friend["end"])
        min_duration = int(friend["min_duration"] * 60)  # convert hours to minutes
        meet_vars.append({
            "name": friend["name"],
            "district": friend["district"],
            "start_var": start_var,
            "end_var": end_var,
            "min_duration": min_duration,
            "availability_start": availability_start,
            "availability_end": availability_end
        })
        # Constraints: meeting within availability and duration
        s.add(start_var >= availability_start)
        s.add(end_var <= availability_end)
        s.add(end_var - start_var >= min_duration)

    # Constraints for travel times between meetings
    for i in range(len(meet_vars)):
        for j in range(len(meet_vars)):
            if i != j:
                # If meeting i is before meeting j
                from_dist = districts[meet_vars[i]["district"]]
                to_dist = districts[meet_vars[j]["district"]]
                travel_time = travel_times[from_dist][to_dist]
                s.add(Or(
                    meet_vars[j]["start_var"] >= meet_vars[i]["end_var"] + travel_time,
                    meet_vars[i]["start_var"] >= meet_vars[j]["end_var"] + travel_times[to_dist][from_dist]
                ))

    # Initial location: Richmond District at time 0 (9:00 AM)
    # First meeting must account for travel from Richmond
    for i in range(len(meet_vars)):
        from_dist = 0  # Richmond District
        to_dist = districts[meet_vars[i]["district"]]
        travel_time = travel_times[from_dist][to_dist]
        s.add(meet_vars[i]["start_var"] >= travel_time)

    # Try to meet all friends
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meet in meet_vars:
            start_val = model.evaluate(meet["start_var"]).as_long()
            end_val = model.evaluate(meet["end_var"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": meet["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))