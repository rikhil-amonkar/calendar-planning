from z3 import *
import json

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
        solver.add(start + duration <= (avail_end - 9*60))
        # Meeting duration must be at least the minimum
        solver.add(duration >= durations[name])

    # Current location starts at Embarcadero at time 0 (9:00 AM)
    current_location = 'Embarcadero'
    current_time = 0

    # We need to model the sequence of meetings with travel times
    # For simplicity, we'll create an order constraint between meetings
    # and ensure travel time is accounted for between consecutive meetings

    # Create all possible meeting pairs
    from itertools import permutations
    for (name1, loc1, _, _, _), (name2, loc2, _, _, _) in permutations(friends, 2):
        if name1 == name2:
            continue
        
        # Get travel time between locations
        travel_time = travel_times.get((loc1, loc2), None)
        if travel_time is None:
            travel_time = travel_times.get((loc2, loc1), None)
        
        if travel_time is not None:
            # If meeting1 is before meeting2, ensure enough time to travel
            solver.add(Or(
                meeting_vars[name1] + durations[name1] + travel_time <= meeting_vars[name2],
                meeting_vars[name2] + durations[name2] + travel_time <= meeting_vars[name1]
            ))

    # Special constraint: must meet Kenneth in the evening
    solver.add(meeting_vars['Kenneth'] >= (21*60 + 15 - 9*60))

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in meeting_vars:
            start_minutes = model.evaluate(meeting_vars[name]).as_long()
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
        
        # Verify no overlapping meetings after accounting for travel
        valid = True
        for i in range(len(itinerary)-1):
            current = itinerary[i]
            next_meeting = itinerary[i+1]
            
            # Find travel time between current and next location
            current_loc = next(friend[1] for friend in friends if friend[0] == current["person"])
            next_loc = next(friend[1] for friend in friends if friend[0] == next_meeting["person"])
            
            travel_time = travel_times.get((current_loc, next_loc), 
                         travel_times.get((next_loc, current_loc), 0))
            
            # Check if there's enough time between meetings
            current_end = int(current["end_time"][:2])*60 + int(current["end_time"][3:])
            next_start = int(next_meeting["start_time"][:2])*60 + int(next_meeting["start_time"][3:])
            
            if current_end + travel_time > next_start:
                valid = False
                break
        
        if valid:
            return {"itinerary": itinerary}
        else:
            # If the solution isn't valid, try again with additional constraints
            return {"itinerary": []}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))