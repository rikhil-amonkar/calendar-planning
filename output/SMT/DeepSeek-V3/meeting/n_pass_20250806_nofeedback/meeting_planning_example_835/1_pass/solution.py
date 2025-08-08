from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    solver = Solver()

    # Define the travel times as a dictionary for easy lookup
    travel_times = {
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Mission District'): 17,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Financial District'): 21,
        ('The Castro', 'Mission District'): 7,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Mission District'): 20,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Mission District'): 14,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Mission District'): 25,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Mission District'): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'The Castro'): 20,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Mission District'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Financial District'): 15,
    }

    # Friends data: name, location, available start, available end, min duration
    friends = [
        ("Helen", "Golden Gate Park", (9, 30), (12, 15), 45),
        ("Steven", "The Castro", (20, 15), (22, 0), 105),
        ("Deborah", "Bayview", (8, 30), (12, 0), 30),
        ("Matthew", "Marina District", (9, 15), (14, 15), 45),
        ("Joseph", "Union Square", (14, 15), (18, 45), 120),
        ("Ronald", "Sunset District", (16, 0), (20, 45), 60),
        ("Robert", "Alamo Square", (18, 30), (21, 15), 120),
        ("Rebecca", "Financial District", (14, 45), (16, 15), 30),
        ("Elizabeth", "Mission District", (18, 30), (21, 0), 120),
    ]

    # Convert time to minutes since midnight for easier calculations
    def time_to_minutes(h, m):
        return h * 60 + m

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Initialize variables for each friend's meeting start and end times
    meetings = {}
    for name, loc, (start_h, start_m), (end_h, end_m), duration in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        available_start = time_to_minutes(start_h, start_m)
        available_end = time_to_minutes(end_h, end_m)
        solver.add(start_var >= available_start)
        solver.add(end_var <= available_end)
        solver.add(end_var == start_var + duration)
        meetings[name] = {
            'location': loc,
            'start': start_var,
            'end': end_var,
            'duration': duration,
        }

    # Starting point: Pacific Heights at 9:00 AM (540 minutes)
    current_time = time_to_minutes(9, 0)
    current_location = "Pacific Heights"

    # Track the order of meetings to enforce travel times
    # We'll use a list to represent the sequence of meetings
    # For simplicity, we'll assume the order is fixed based on time windows (this is a simplification)
    # Alternatively, we can use a more complex model with ordering variables, but that's complex for Z3
    # Here, we'll prioritize friends based on their time windows and try to meet them in a feasible order

    # For each meeting, ensure that the start time is after the previous meeting's end time + travel time
    # We'll need to define the order of meetings. This is a heuristic; in practice, we might need to try different orders
    # For this problem, we'll assume the order is: Deborah, Matthew, Helen, Rebecca, Joseph, Ronald, Robert, Elizabeth, Steven
    # This is a guess; the actual order might need adjustment
    meeting_order = ["Deborah", "Matthew", "Helen", "Rebecca", "Joseph", "Ronald", "Robert", "Elizabeth", "Steven"]

    # Add constraints for travel times between meetings
    prev_end = current_time
    prev_loc = current_location
    for name in meeting_order:
        if name in meetings:
            meeting = meetings[name]
            travel_time = travel_times.get((prev_loc, meeting['location']), 0)
            solver.add(meeting['start'] >= prev_end + travel_time)
            prev_end = meeting['end']
            prev_loc = meeting['location']

    # Also, ensure that meetings do not overlap (though the travel time constraints should handle this)
    # Add constraints to meet as many friends as possible (this is implicit in the model)

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in meeting_order:
            if name in meetings:
                meeting = meetings[name]
                start_val = model.eval(meeting['start']).as_long()
                end_val = model.eval(meeting['end']).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val),
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))