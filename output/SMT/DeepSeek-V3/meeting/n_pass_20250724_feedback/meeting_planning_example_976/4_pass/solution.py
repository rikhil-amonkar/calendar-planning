from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver with optimization
    s = Optimize()

    # Define travel times (simplified to symmetric for this example)
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
        # Reverse directions (assuming symmetric for simplicity)
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

    # Friend data with simplified constraints
    friends = [
        {"name": "Stephanie", "location": "Presidio", "start": 7*60+30, "end": 10*60+15, "duration": 60},
        {"name": "Brian", "location": "Marina District", "start": 12*60+15, "end": 18*60, "duration": 60},
        {"name": "Thomas", "location": "Fisherman\'s Wharf", "start": 13*60+30, "end": 19*60, "duration": 30},
        {"name": "Nancy", "location": "North Beach", "start": 14*60+45, "end": 20*60, "duration": 15},
        {"name": "Jessica", "location": "Nob Hill", "start": 16*60+30, "end": 18*60+45, "duration": 60},
        {"name": "Mary", "location": "Union Square", "start": 16*60+45, "end": 21*60+30, "duration": 60},
        {"name": "Charles", "location": "The Castro", "start": 16*60+30, "end": 22*60, "duration": 60},
        {"name": "Karen", "location": "Chinatown", "start": 19*60+15, "end": 21*60+15, "duration": 60},
        {"name": "Matthew", "location": "Bayview", "start": 19*60+15, "end": 22*60, "duration": 60},
        {"name": "Sarah", "location": "Alamo Square", "start": 20*60, "end": 21*60+45, "duration": 60},
    ]

    # Current location starts at Embarcadero at 9:00 AM (540 minutes)
    current_location = "Embarcadero"
    current_time = 9 * 60

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        s.add(start_var >= friend["start"])
        s.add(end_var <= friend["end"])
        s.add(end_var - start_var >= friend["duration"])
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "duration": friend["duration"]
        })

    # Add ordering constraints
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]
            travel_time = travel_times.get((m1["location"], m2["location"]), 0)
            s.add(Or(
                m1["end_var"] + travel_time <= m2["start_var"],
                m2["end_var"] + travel_time <= m1["start_var"]
            ))

    # Ensure first meeting is reachable
    for meeting in meetings:
        travel_time = travel_times.get((current_location, meeting["location"]), 0)
        s.add(meeting["start_var"] >= current_time + travel_time)

    # Maximize number of friends met
    s.maximize(Sum([If(And(meeting["start_var"] >= 0, meeting["end_var"] >= 0), 1, 0) for meeting in meetings]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start = model.evaluate(meeting["start_var"])
            end = model.evaluate(meeting["end_var"])
            if start.as_long() != 0 and end.as_long() != 0:
                start_time = f"{start.as_long() // 60:02d}:{start.as_long() % 60:02d}"
                end_time = f"{end.as_long() // 60:02d}:{end.as_long() % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))