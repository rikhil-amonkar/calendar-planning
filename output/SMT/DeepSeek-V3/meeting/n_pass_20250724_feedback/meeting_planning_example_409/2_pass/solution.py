from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer (instead of Solver)
    opt = Optimize()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Marina District'): 25,
        ('Bayview', 'Embarcadero'): 19,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Embarcadero'): 14,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Marina District'): 12,
    }

    # Friend data: name, location, available start, available end, min duration
    friends = [
        ('Thomas', 'Bayview', 15 * 60 + 30, 18 * 60 + 30, 120),
        ('Stephanie', 'Golden Gate Park', 18 * 60 + 30, 21 * 60 + 45, 30),
        ('Laura', 'Nob Hill', 8 * 60 + 45, 16 * 60 + 15, 30),
        ('Betty', 'Marina District', 18 * 60 + 45, 21 * 60 + 45, 45),
        ('Patricia', 'Embarcadero', 17 * 60 + 30, 22 * 60 + 0, 45),
    ]

    # Current location starts at Fisherman's Wharf at 9:00 AM (540 minutes)
    current_location = 'Fisherman\'s Wharf'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Variables to track meetings
    itinerary = []
    meet_vars = []

    # For each friend, create variables for meeting start and end times
    for friend in friends:
        name, location, avail_start, avail_end, min_duration = friend
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet = Bool(f'meet_{name}')

        # Constraints for meeting times
        opt.add(Implies(meet, start >= avail_start))
        opt.add(Implies(meet, end <= avail_end))
        opt.add(Implies(meet, end == start + min_duration))
        opt.add(Implies(meet, start >= current_time + travel_times.get((current_location, location), 0)))

        # Add to meet_vars and itinerary if meeting is scheduled
        meet_vars.append(meet)
        itinerary.append((name, location, start, end, meet))

    # Ensure at least one meeting is scheduled
    opt.add(Or(*meet_vars))

    # Maximize the number of meetings
    opt.maximize(Sum([If(meet, 1, 0) for meet in meet_vars]))

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        result = []
        for name, location, start, end, meet in itinerary:
            if model.evaluate(meet):
                start_val = model.evaluate(start).as_long()
                end_val = model.evaluate(end).as_long()
                start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
                result.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        return {"itinerary": result}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
solution = solve_scheduling()
print(json.dumps(solution, indent=2))