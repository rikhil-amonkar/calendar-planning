from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define friends and their constraints
    friends = [
        {"name": "Matthew", "location": "The Castro", "start": "16:30", "end": "20:00", "duration": 45},
        {"name": "Rebecca", "location": "Nob Hill", "start": "15:15", "end": "19:15", "duration": 105},
        {"name": "Brian", "location": "Marina District", "start": "14:15", "end": "22:00", "duration": 30},
        {"name": "Emily", "location": "Pacific Heights", "start": "11:15", "end": "19:45", "duration": 15},
        {"name": "Karen", "location": "Haight-Ashbury", "start": "11:45", "end": "17:30", "duration": 30},
        {"name": "Stephanie", "location": "Mission District", "start": "13:00", "end": "15:45", "duration": 75},
        {"name": "James", "location": "Chinatown", "start": "14:30", "end": "19:00", "duration": 120},
        {"name": "Steven", "location": "Russian Hill", "start": "14:00", "end": "20:00", "duration": 30},
        {"name": "Elizabeth", "location": "Alamo Square", "start": "13:00", "end": "17:15", "duration": 120},
        {"name": "William", "location": "Bayview", "start": "18:15", "end": "20:15", "duration": 90}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Complete travel times dictionary
    travel_times = {
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Bayview"): 27,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Bayview"): 19,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Bayview"): 27,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Bayview"): 22,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Bayview"): 14,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 20,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Bayview"): 23,
        ("Alamo Square", "Bayview"): 16
    }

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        duration = friend["duration"]
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        
        opt.add(start_var >= start_window)
        opt.add(end_var <= end_window)
        opt.add(end_var == start_var + duration)
        opt.add(start_var >= 0)
        
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "duration": duration
        })

    # Create meeting order variables
    n = len(meetings)
    order = [Int(f"order_{i}") for i in range(n)]
    opt.add(Distinct(order))
    opt.add([And(order[i] >= 0, order[i] < n) for i in range(n)])

    # Add sequencing constraints
    for i in range(n):
        for j in range(n):
            if i != j:
                # If meeting i comes before meeting j
                before = Bool(f"before_{i}_{j}")
                opt.add(before == (order[i] < order[j]))
                
                # Travel time between locations
                travel = travel_times.get((meetings[i]["location"], meetings[j]["location"]), 0)
                
                # Ensure sufficient time between meetings
                opt.add(Implies(before, meetings[j]["start_var"] >= meetings[i]["end_var"] + travel))

    # Maximize number of meetings (alternative: sum of durations)
    meeting_flags = [Bool(f"meet_{m['name']}") for m in meetings]
    for i in range(n):
        opt.add(meeting_flags[i] == (order[i] >= 0))  # All meetings are scheduled
    opt.maximize(Sum([If(meeting_flags[i], 1, 0) for i in range(n)]))

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        # Get meetings in order
        ordered_meetings = sorted([(model.eval(order[i]), meetings[i]) for i in range(n)], key=lambda x: x[0].as_long())
        itinerary = []
        for _, meeting in ordered_meetings:
            start = model.eval(meeting["start_var"]).as_long()
            end = model.eval(meeting["end_var"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))