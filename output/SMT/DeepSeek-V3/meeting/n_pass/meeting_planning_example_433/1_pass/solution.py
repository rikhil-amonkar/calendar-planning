from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Golden Gate Park'): 23,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 20,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
    }

    # Friends' data: name, location, availability start and end, min duration
    friends = [
        ('Emily', 'Richmond District', time_to_minutes('19:00'), time_to_minutes('21:00'), 15),
        ('Margaret', 'Financial District', time_to_minutes('16:30'), time_to_minutes('20:15'), 75),
        ('Ronald', 'North Beach', time_to_minutes('18:30'), time_to_minutes('19:30'), 45),
        ('Deborah', 'The Castro', time_to_minutes('13:45'), time_to_minutes('21:15'), 90),
        ('Jeffrey', 'Golden Gate Park', time_to_minutes('11:15'), time_to_minutes('14:30'), 120),
    ]

    # Create variables for each friend's meeting start and end times
    meet_vars = []
    for name, loc, avail_start, avail_end, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= avail_start)
        s.add(end <= avail_end)
        s.add(end == start + min_dur)
        meet_vars.append((name, loc, start, end))

    # Define the order of meetings (since we can't meet all, prioritize based on constraints)
    # We'll try to meet as many as possible, starting with the earliest possible meetings.

    # Add travel time constraints between consecutive meetings
    # We need to define the sequence of meetings. Here, we'll assume a possible order and adjust.
    # For simplicity, let's try to meet Jeffrey first, then Deborah, then Margaret, then Ronald, then Emily.
    # This is a heuristic; the solver will adjust if this order is infeasible.

    # Define the order: Jeffrey -> Deborah -> Margaret -> Ronald -> Emily
    # We'll need to ensure that the end time of one meeting + travel <= start time of next.

    # Extract the variables in the desired order
    order = ['Jeffrey', 'Deborah', 'Margaret', 'Ronald', 'Emily']
    ordered_meets = []
    for name in order:
        for meet in meet_vars:
            if meet[0] == name:
                ordered_meets.append(meet)
                break

    # Add travel constraints between consecutive meetings
    for i in range(len(ordered_meets) - 1):
        current = ordered_meets[i]
        next_meet = ordered_meets[i+1]
        current_loc = current[1]
        next_loc = next_meet[1]
        travel_time = travel_times[(current_loc, next_loc)]
        s.add(next_meet[2] >= current[3] + travel_time)

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, loc, start_var, end_var in meet_vars:
            start_val = model.evaluate(start_var).as_long()
            end_val = model.evaluate(end_var).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))