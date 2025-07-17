from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Presidio'): 10,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Presidio'): 7,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Presidio'): 24,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Presidio'): 20,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Presidio'): 22,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Presidio'): 17,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'North Beach'): 18,
    }

    # Define the friends and their constraints
    friends = [
        {"name": "Stephanie", "location": "Richmond District", "available_start": "16:15", "available_end": "21:30", "duration": 75},
        {"name": "William", "location": "Union Square", "available_start": "10:45", "available_end": "17:30", "duration": 45},
        {"name": "Elizabeth", "location": "Nob Hill", "available_start": "12:15", "available_end": "15:00", "duration": 105},
        {"name": "Joseph", "location": "Fisherman's Wharf", "available_start": "12:45", "available_end": "14:00", "duration": 75},
        {"name": "Anthony", "location": "Golden Gate Park", "available_start": "13:00", "available_end": "20:30", "duration": 75},
        {"name": "Barbara", "location": "Embarcadero", "available_start": "19:15", "available_end": "20:30", "duration": 75},
        {"name": "Carol", "location": "Financial District", "available_start": "11:45", "available_end": "16:15", "duration": 60},
        {"name": "Sandra", "location": "North Beach", "available_start": "10:00", "available_end": "12:30", "duration": 15},
        {"name": "Kenneth", "location": "Presidio", "available_start": "21:15", "available_end": "22:15", "duration": 45},
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    for friend in friends:
        friend["available_start_min"] = time_to_minutes(friend["available_start"])
        friend["available_end_min"] = time_to_minutes(friend["available_end"])

    # Define variables for each meeting's start and end times
    meetings = []
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        s.add(start >= friend["available_start_min"])
        s.add(end <= friend["available_end_min"])
        s.add(end == start + friend["duration"])
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "duration": friend["duration"]
        })

    # Define a binary variable for each pair of meetings indicating which comes first
    num_meetings = len(meetings)
    before = [[Bool(f'before_{i}_{j}') for j in range(num_meetings)] for i in range(num_meetings)]

    # Add constraints for the ordering variables
    for i in range(num_meetings):
        for j in range(num_meetings):
            if i != j:
                s.add(Implies(before[i][j], Not(before[j][i])))  # Anti-symmetry
                s.add(Or(before[i][j], before[j][i]))  # Total ordering
                # Transitivity
                for k in range(num_meetings):
                    if k != i and k != j:
                        s.add(Implies(And(before[i][j], before[j][k]), before[i][k]))

    # Add travel time constraints
    for i in range(num_meetings):
        for j in range(num_meetings):
            if i != j:
                loc_i = meetings[i]["location"]
                loc_j = meetings[j]["location"]
                travel_time = travel_times.get((loc_i, loc_j), 0)
                s.add(Implies(before[i][j], meetings[j]["start"] >= meetings[i]["end"] + travel_time))

    # Ensure all meetings are scheduled
    for meeting in meetings:
        s.add(meeting["start"] >= 0)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start_time = model[meeting["start"]].as_long()
            end_time = model[meeting["end"]].as_long()
            start_hh = (start_time + 540) // 60
            start_mm = (start_time + 540) % 60
            end_hh = (end_time + 540) // 60
            end_mm = (end_time + 540) % 60
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))