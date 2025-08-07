from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Russian Hill'): 8,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Russian Hill'): 18,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Russian Hill'): 13,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Russian Hill'): 4,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Russian Hill'): 7,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Russian Hill'): 8,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Marina District'): 7,
    }

    # Define friends and their constraints
    friends = [
        {"name": "Mary", "location": "Embarcadero", "start": 20*60, "end": 21*60 + 15, "duration": 75},
        {"name": "Kenneth", "location": "The Castro", "start": 11*60 + 15, "end": 19*60 + 15, "duration": 30},
        {"name": "Joseph", "location": "Haight-Ashbury", "start": 20*60, "end": 22*60, "duration": 120},
        {"name": "Sarah", "location": "Union Square", "start": 11*60 + 45, "end": 14*60 + 30, "duration": 90},
        {"name": "Thomas", "location": "North Beach", "start": 19*60 + 15, "end": 19*60 + 45, "duration": 15},
        {"name": "Daniel", "location": "Pacific Heights", "start": 13*60 + 45, "end": 20*60 + 30, "duration": 15},
        {"name": "Richard", "location": "Chinatown", "start": 8*60, "end": 18*60 + 45, "duration": 30},
        {"name": "Mark", "location": "Golden Gate Park", "start": 17*60 + 30, "end": 21*60 + 30, "duration": 120},
        {"name": "David", "location": "Marina District", "start": 20*60, "end": 21*60, "duration": 60},
        {"name": "Karen", "location": "Russian Hill", "start": 13*60 + 15, "end": 18*60 + 30, "duration": 120},
    ]

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        s.add(start >= friend["start"])
        s.add(end <= friend["end"])
        s.add(end == start + friend["duration"])
        meetings.append({"name": friend["name"], "location": friend["location"], "start": start, "end": end})

    # Create ordering variables to help the solver
    order = [Int(f"order_{friend['name']}") for friend in friends]
    s.add(Distinct(order))
    for i in range(len(friends)):
        s.add(order[i] >= 0, order[i] < len(friends))

    # Initial location is Nob Hill at 9:00 AM (540 minutes)
    current_location = "Nob Hill"
    current_time = 9 * 60

    # Add constraints based on ordering
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                # If meeting i comes before meeting j in order, add travel time constraint
                s.add(Implies(
                    order[i] < order[j],
                    meetings[i]["end"] + travel_times[(meetings[i]["location"], meetings[j]["location"])] <= meetings[j]["start"]
                ))

    # Ensure the first meeting is after current_time plus travel time from Nob Hill
    for i in range(len(meetings)):
        s.add(Implies(
            order[i] == 0,
            meetings[i]["start"] >= current_time + travel_times[(current_location, meetings[i]["location"])]
        ))

    # Maximize the number of meetings (optional)
    # s.maximize(Sum([If(meetings[i]["start"] >= 0, 1, 0) for i in range(len(meetings))]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start_time = model[meeting["start"]].as_long()
            end_time = model[meeting["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": f"{start_time // 60:02d}:{start_time % 60:02d}",
                "end_time": f"{end_time // 60:02d}:{end_time % 60:02d}"
            })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:5])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))