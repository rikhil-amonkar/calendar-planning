from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define friends and their constraints
    friends = {
        "Elizabeth": {
            "location": "Sunset District",
            "available_start": "09:00",
            "available_end": "09:45",
            "min_duration": 45,
        },
        "Joseph": {
            "location": "Chinatown",
            "available_start": "07:00",
            "available_end": "15:30",
            "min_duration": 60,
        },
        "Carol": {
            "location": "Financial District",
            "available_start": "10:45",
            "available_end": "11:15",
            "min_duration": 15,
        },
        "Matthew": {
            "location": "Golden Gate Park",
            "available_start": "11:00",
            "available_end": "19:30",
            "min_duration": 45,
        },
        "Charles": {
            "location": "Union Square",
            "available_start": "10:45",
            "available_end": "20:15",
            "min_duration": 120,
        },
        "Joshua": {
            "location": "Embarcadero",
            "available_start": "09:45",
            "available_end": "18:00",
            "min_duration": 105,
        },
        "Jeffrey": {
            "location": "Bayview",
            "available_start": "09:45",
            "available_end": "20:15",
            "min_duration": 75,
        },
        "Rebecca": {
            "location": "Mission District",
            "available_start": "17:00",
            "available_end": "21:45",
            "min_duration": 45,
        },
        "Paul": {
            "location": "Haight-Ashbury",
            "available_start": "19:15",
            "available_end": "20:30",
            "min_duration": 15,
        },
    }

    # Travel times between locations (in minutes)
    travel_times = {
        "Sunset District": {
            "Chinatown": 29,
            "Financial District": 30,
            "Golden Gate Park": 11,
        },
        "Chinatown": {
            "Financial District": 5,
            "Golden Gate Park": 23,
            "Union Square": 7,
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Union Square": 9,
            "Embarcadero": 5,
        },
        "Golden Gate Park": {
            "Union Square": 22,
            "Embarcadero": 25,
            "Bayview": 23,
        },
        "Union Square": {
            "Embarcadero": 10,
            "Bayview": 15,
            "Mission District": 14,
        },
        "Embarcadero": {
            "Bayview": 21,
            "Mission District": 20,
            "Haight-Ashbury": 21,
        },
        "Bayview": {
            "Mission District": 13,
            "Haight-Ashbury": 19,
        },
        "Mission District": {
            "Haight-Ashbury": 12,
        },
    }

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540

    def minutes_to_time(minutes):
        total = 540 + minutes
        return f"{total//60:02d}:{total%60:02d}"

    # Create meeting variables
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = (start, end)
        # Basic constraints
        solver.add(start >= time_to_minutes(friends[name]["available_start"]))
        solver.add(end <= time_to_minutes(friends[name]["available_end"]))
        solver.add(end - start >= friends[name]["min_duration"])

    # Fixed meeting with Elizabeth at 9:00 AM
    solver.add(meetings["Elizabeth"][0] == 0)  # 9:00 AM is 0 minutes after 9:00 AM
    solver.add(meetings["Elizabeth"][1] == 45)

    # Define meeting order
    order = ["Elizabeth", "Joseph", "Carol", "Matthew", "Charles", "Joshua", "Jeffrey", "Rebecca", "Paul"]

    # Add travel time constraints between consecutive meetings
    for i in range(len(order)-1):
        current = order[i]
        next_ = order[i+1]
        travel = travel_times[friends[current]["location"]][friends[next_]["location"]]
        solver.add(meetings[next_][0] >= meetings[current][1] + travel)

    # Special constraints for Carol (short window)
    solver.add(meetings["Carol"][0] >= time_to_minutes("10:45"))
    solver.add(meetings["Carol"][1] <= time_to_minutes("11:15"))

    # Special constraints for Paul (evening window)
    solver.add(meetings["Paul"][0] >= time_to_minutes("19:15"))
    solver.add(meetings["Paul"][1] <= time_to_minutes("20:30"))

    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in order:
            start = model.eval(meetings[name][0]).as_long()
            end = model.eval(meetings[name][1]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))