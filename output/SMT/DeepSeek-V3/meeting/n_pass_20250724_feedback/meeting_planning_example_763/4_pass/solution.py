from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Friends data with constraints
    friends = {
        "Richard": {"location": "Embarcadero", "available_start": "15:15", "available_end": "18:45", "min_duration": 90},
        "Mark": {"location": "Pacific Heights", "available_start": "15:00", "available_end": "17:00", "min_duration": 45},
        "Matthew": {"location": "Russian Hill", "available_start": "17:30", "available_end": "21:00", "min_duration": 90},
        "Rebecca": {"location": "Haight-Ashbury", "available_start": "14:45", "available_end": "18:00", "min_duration": 60},
        "Melissa": {"location": "Golden Gate Park", "available_start": "13:45", "available_end": "17:30", "min_duration": 90},
        "Margaret": {"location": "Fisherman's Wharf", "available_start": "14:45", "available_end": "20:15", "min_duration": 15},
        "Emily": {"location": "Sunset District", "available_start": "15:45", "available_end": "17:00", "min_duration": 45},
        "George": {"location": "The Castro", "available_start": "14:00", "available_end": "16:15", "min_duration": 75}
    }

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540

    def minutes_to_time(minutes):
        total = 540 + minutes
        return f"{total//60:02d}:{total%60:02d}"

    # Travel times (from -> to -> minutes)
    travel = {
        "Chinatown": {"Embarcadero":5, "Pacific Heights":10, "Russian Hill":7, "Haight-Ashbury":19, 
                     "Golden Gate Park":23, "Fisherman's Wharf":8, "Sunset District":29, "The Castro":22},
        "Embarcadero": {"Chinatown":7, "Pacific Heights":11, "Russian Hill":8, "Haight-Ashbury":21,
                       "Golden Gate Park":25, "Fisherman's Wharf":6, "Sunset District":30, "The Castro":25},
        "Pacific Heights": {"Chinatown":11, "Embarcadero":10, "Russian Hill":7, "Haight-Ashbury":11,
                          "Golden Gate Park":15, "Fisherman's Wharf":13, "Sunset District":21, "The Castro":16},
        "Russian Hill": {"Chinatown":9, "Embarcadero":8, "Pacific Heights":7, "Haight-Ashbury":17,
                       "Golden Gate Park":21, "Fisherman's Wharf":7, "Sunset District":23, "The Castro":21},
        "Haight-Ashbury": {"Chinatown":19, "Embarcadero":20, "Pacific Heights":12, "Russian Hill":17,
                         "Golden Gate Park":7, "Fisherman's Wharf":23, "Sunset District":15, "The Castro":6},
        "Golden Gate Park": {"Chinatown":23, "Embarcadero":25, "Pacific Heights":16, "Russian Hill":19,
                           "Haight-Ashbury":7, "Fisherman's Wharf":24, "Sunset District":10, "The Castro":13},
        "Fisherman's Wharf": {"Chinatown":12, "Embarcadero":8, "Pacific Heights":12, "Russian Hill":7,
                            "Haight-Ashbury":22, "Golden Gate Park":25, "Sunset District":27, "The Castro":27},
        "Sunset District": {"Chinatown":30, "Embarcadero":30, "Pacific Heights":21, "Russian Hill":24,
                          "Haight-Ashbury":15, "Golden Gate Park":11, "Fisherman's Wharf":29, "The Castro":17},
        "The Castro": {"Chinatown":22, "Embarcadero":22, "Pacific Heights":16, "Russian Hill":18,
                     "Haight-Ashbury":6, "Golden Gate Park":11, "Fisherman's Wharf":24, "Sunset District":17}
    }

    # Create meeting variables
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {"start": start, "end": end}

    # Basic meeting constraints
    for name, data in friends.items():
        start_min = time_to_minutes(data["available_start"])
        end_max = time_to_minutes(data["available_end"])
        min_dur = data["min_duration"]
        
        s.add(meetings[name]["start"] >= start_min)
        s.add(meetings[name]["end"] <= end_max)
        s.add(meetings[name]["end"] - meetings[name]["start"] >= min_dur)

    # Define meeting order (we'll try multiple orders)
    orders_to_try = [
        ["Melissa", "George", "Rebecca", "Mark", "Richard", "Emily", "Margaret", "Matthew"],
        ["George", "Melissa", "Rebecca", "Mark", "Richard", "Emily", "Margaret", "Matthew"],
        ["Melissa", "George", "Margaret", "Rebecca", "Mark", "Richard", "Emily", "Matthew"]
    ]

    for order in orders_to_try:
        temp_solver = Solver()
        
        # Add basic constraints
        for name, data in friends.items():
            start_min = time_to_minutes(data["available_start"])
            end_max = time_to_minutes(data["available_end"])
            min_dur = data["min_duration"]
            temp_solver.add(meetings[name]["start"] >= start_min)
            temp_solver.add(meetings[name]["end"] <= end_max)
            temp_solver.add(meetings[name]["end"] - meetings[name]["start"] >= min_dur)

        # Add travel constraints for this order
        for i in range(len(order)-1):
            current = order[i]
            next_p = order[i+1]
            current_loc = friends[current]["location"]
            next_loc = friends[next_p]["location"]
            travel_time = travel[current_loc][next_loc]
            temp_solver.add(meetings[next_p]["start"] >= meetings[current]["end"] + travel_time)

        # Try to solve
        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            for name in order:
                start = model[meetings[name]["start"]].as_long()
                end = model[meetings[name]["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
            return {"itinerary": itinerary}

    return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))