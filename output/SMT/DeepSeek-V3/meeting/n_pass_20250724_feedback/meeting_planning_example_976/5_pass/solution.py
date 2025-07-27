from z3 import *
import json
from itertools import combinations

def solve_scheduling_problem():
    s = Optimize()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Marina District'): 12,
        # Reverse directions (assuming symmetric)
        ('Bayview', 'Embarcadero'): 21,
        ('Chinatown', 'Embarcadero'): 7,
        ('Alamo Square', 'Embarcadero'): 19,
        ('Nob Hill', 'Embarcadero'): 10,
        ('Presidio', 'Embarcadero'): 20,
        ('Union Square', 'Embarcadero'): 10,
        ('The Castro', 'Embarcadero'): 25,
        ('North Beach', 'Embarcadero'): 5,
        ('Fisherman\'s Wharf', 'Embarcadero'): 6,
        ('Marina District', 'Embarcadero'): 12,
    }

    # Friend data with relaxed constraints
    friends = [
        {"name": "Stephanie", "location": "Presidio", "start": 450, "end": 615, "duration": 60},
        {"name": "Brian", "location": "Marina District", "start": 735, "end": 1080, "duration": 60},
        {"name": "Thomas", "location": "Fisherman\'s Wharf", "start": 810, "end": 1140, "duration": 30},
        {"name": "Nancy", "location": "North Beach", "start": 885, "end": 1200, "duration": 15},
        {"name": "Jessica", "location": "Nob Hill", "start": 990, "end": 1125, "duration": 60},
        {"name": "Mary", "location": "Union Square", "start": 1005, "end": 1290, "duration": 60},
        {"name": "Charles", "location": "The Castro", "start": 990, "end": 1320, "duration": 60},
        {"name": "Karen", "location": "Chinatown", "start": 1155, "end": 1275, "duration": 60},
        {"name": "Matthew", "location": "Bayview", "start": 1155, "end": 1320, "duration": 60},
        {"name": "Sarah", "location": "Alamo Square", "start": 1200, "end": 1305, "duration": 60},
    ]

    # Create meeting variables
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        s.add(start >= friend["start"])
        s.add(end <= friend["end"])
        s.add(end - start >= friend["duration"])
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end
        })

    # Add ordering constraints
    for m1, m2 in combinations(meetings, 2):
        travel = travel_times.get((m1["location"], m2["location"]), 0)
        s.add(Or(
            m1["end"] + travel <= m2["start"],
            m2["end"] + travel <= m1["start"]
        ))

    # Starting constraints
    current_time = 540  # 9:00 AM
    current_loc = "Embarcadero"
    for m in meetings:
        travel = travel_times.get((current_loc, m["location"]), 0)
        s.add(m["start"] >= current_time + travel)

    # Maximize number of meetings
    meeting_vars = [If(And(m["start"] >= 0, m["end"] >= 0), 1, 0) for m in meetings]
    s.maximize(Sum(meeting_vars))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for m in meetings:
            start = model.evaluate(m["start"])
            end = model.evaluate(m["end"])
            if start.as_long() > 0:
                start_time = f"{start.as_long()//60:02d}:{start.as_long()%60:02d}"
                end_time = f"{end.as_long()//60:02d}:{end.as_long()%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": m["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))