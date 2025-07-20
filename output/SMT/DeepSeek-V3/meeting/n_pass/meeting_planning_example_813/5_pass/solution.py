from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define friends data with availability and duration requirements
    friends = {
        "Elizabeth": {"location": "Sunset District", "start": "09:00", "end": "09:45", "duration": 45},
        "Joseph": {"location": "Chinatown", "start": "07:00", "end": "15:30", "duration": 60},
        "Carol": {"location": "Financial District", "start": "10:45", "end": "11:15", "duration": 15},
        "Matthew": {"location": "Golden Gate Park", "start": "11:00", "end": "19:30", "duration": 45},
        "Charles": {"location": "Union Square", "start": "10:45", "end": "20:15", "duration": 120},
        "Joshua": {"location": "Embarcadero", "start": "09:45", "end": "18:00", "duration": 105},
        "Jeffrey": {"location": "Bayview", "start": "09:45", "end": "20:15", "duration": 75},
        "Rebecca": {"location": "Mission District", "start": "17:00", "end": "21:45", "duration": 45},
        "Paul": {"location": "Haight-Ashbury", "start": "19:15", "end": "20:30", "duration": 15},
    }

    # Travel times between locations (in minutes)
    travel = {
        "Sunset District": {"Chinatown": 29, "Financial District": 30, "Golden Gate Park": 11},
        "Chinatown": {"Financial District": 5, "Golden Gate Park": 23, "Union Square": 7},
        "Financial District": {"Golden Gate Park": 23, "Union Square": 9, "Embarcadero": 5},
        "Golden Gate Park": {"Union Square": 22, "Embarcadero": 25, "Bayview": 23},
        "Union Square": {"Embarcadero": 10, "Bayview": 15, "Mission District": 14},
        "Embarcadero": {"Bayview": 21, "Mission District": 20, "Haight-Ashbury": 21},
        "Bayview": {"Mission District": 13, "Haight-Ashbury": 19},
        "Mission District": {"Haight-Ashbury": 12},
    }

    # Helper functions for time conversion
    def time_to_min(t):
        h, m = map(int, t.split(':'))
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    def min_to_time(m):
        total = 540 + m
        return f"{total//60:02d}:{total%60:02d}"

    # Create variables for each meeting
    vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        vars[name] = (start, end)
        s.add(start >= time_to_min(friends[name]["start"]))
        s.add(end <= time_to_min(friends[name]["end"]))
        s.add(end - start >= friends[name]["duration"])

    # Fixed meeting with Elizabeth at 9:00 AM
    s.add(vars["Elizabeth"][0] == 0)
    s.add(vars["Elizabeth"][1] == 45)

    # Define meeting order that makes geographic sense
    order = ["Elizabeth", "Joseph", "Carol", "Matthew", "Charles", "Joshua", "Jeffrey", "Rebecca", "Paul"]

    # Add travel time constraints between consecutive meetings
    for i in range(len(order)-1):
        curr = order[i]
        next_ = order[i+1]
        curr_loc = friends[curr]["location"]
        next_loc = friends[next_]["location"]
        s.add(vars[next_][0] >= vars[curr][1] + travel[curr_loc][next_loc])

    # Special constraints for tight windows
    s.add(vars["Carol"][0] >= time_to_min("10:45"))
    s.add(vars["Carol"][1] <= time_to_min("11:15"))
    s.add(vars["Paul"][0] >= time_to_min("19:15"))
    s.add(vars["Paul"][1] <= time_to_min("20:30"))

    # Try to solve
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in order:
            start = m.eval(vars[name][0]).as_long()
            end = m.eval(vars[name][1]).as_long()
            schedule.append({
                "action": "meet",
                "person": name,
                "start_time": min_to_time(start),
                "end_time": min_to_time(end),
            })
        return {"itinerary": schedule}
    else:
        # If no solution found, try relaxing some constraints
        print("No solution found with current constraints")
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))