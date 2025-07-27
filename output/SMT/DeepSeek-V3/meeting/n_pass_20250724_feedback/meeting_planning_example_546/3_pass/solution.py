from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Bayview'): 21,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Bayview'): 26,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Bayview'): 15,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Bayview'): 22,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Bayview'): 19,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Nob Hill'): 20,
    }

    # Friend data: name, location, available start, available end, min duration (minutes)
    friends = [
        ('Kenneth', 'Richmond District', 21*60 + 15, 22*60, 30),
        ('Lisa', 'Union Square', 9*60, 16*60 + 30, 45),
        ('Joshua', 'Financial District', 12*60, 15*60 + 15, 15),
        ('Nancy', 'Pacific Heights', 8*60, 11*60 + 30, 90),
        ('Andrew', 'Nob Hill', 11*60 + 30, 20*60 + 15, 60),
        ('John', 'Bayview', 16*60 + 45, 21*60 + 30, 75),
    ]

    # Initialize Z3 solver
    solver = Solver()

    # Variables for each meeting: start time (in minutes since 9:00 AM)
    meeting_vars = {}
    for name, _, _, _, _ in friends:
        meeting_vars[name] = Int(f'start_{name}')

    # Duration variables (fixed to min duration)
    durations = {name: duration for name, _, _, _, duration in friends}

    # Constraints for each meeting
    for name, location, avail_start, avail_end, duration in friends:
        start = meeting_vars[name]
        # Meeting must start within friend's availability (converted to minutes since 9:00 AM)
        solver.add(start >= (avail_start - 9*60))
        solver.add(start + durations[name] <= (avail_end - 9*60))

    # Initial location is Embarcadero at time 0 (9:00 AM)
    # We need to ensure the first meeting accounts for travel time from Embarcadero
    first_meeting = [name for name in meeting_vars]
    for name in first_meeting:
        location = next(f[1] for f in friends if f[0] == name)
        travel_time = travel_times[('Embarcadero', location)]
        solver.add(Implies(
            meeting_vars[name] == min([meeting_vars[n] for n in meeting_vars]),
            meeting_vars[name] >= travel_time
        ))

    # Constraints for travel between meetings
    for (name1, loc1, _, _, _), (name2, loc2, _, _, _) in permutations(friends, 2):
        if name1 == name2:
            continue
        
        travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1)))
        solver.add(Or(
            meeting_vars[name1] + durations[name1] + travel_time <= meeting_vars[name2],
            meeting_vars[name2] + durations[name2] + travel_time <= meeting_vars[name1]
        ))

    # Special constraint: must meet Kenneth in the evening
    solver.add(meeting_vars['Kenneth'] >= (21*60 + 15 - 9*60))

    # Try to maximize the number of meetings
    # We'll create a variable for each possible meeting and maximize their sum
    met_friends = [Int(f'met_{name}') for name in meeting_vars]
    for name, var in zip(meeting_vars.keys(), met_friends):
        solver.add(Or(var == 0, var == 1))
        solver.add(Implies(var == 1, meeting_vars[name] >= 0))

    solver.maximize(sum(met_friends))

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in meeting_vars:
            start_minutes = model.evaluate(meeting_vars[name]).as_long()
            if start_minutes < 0:  # Skip meetings that weren't scheduled
                continue
            start_hour = (start_minutes + 9*60) // 60
            start_minute = (start_minutes + 9*60) % 60
            end_minutes = start_minutes + durations[name]
            end_hour = (end_minutes + 9*60) // 60
            end_minute = (end_minutes + 9*60) % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}"
            })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        
        # Verify the schedule is valid
        prev_end = 0
        prev_location = 'Embarcadero'
        valid = True
        
        for meeting in itinerary:
            person = meeting['person']
            location = next(f[1] for f in friends if f[0] == person)
            start_time = int(meeting['start_time'][:2])*60 + int(meeting['start_time'][3:]) - 9*60
            
            # Check travel time from previous location
            travel_time = travel_times.get((prev_location, location), 
                         travel_times.get((location, prev_location)))
            
            if start_time < prev_end + travel_time:
                valid = False
                break
                
            prev_end = start_time + durations[person]
            prev_location = location
        
        if valid:
            return {"itinerary": itinerary}
        else:
            # If invalid, try again with additional constraints
            return {"itinerary": []}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))