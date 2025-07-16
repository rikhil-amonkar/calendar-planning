from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')
    david_start = Int('david_start')
    david_end = Int('david_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')

    # Travel times (minutes)
    travel_times = {
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Richmond'): 21,
        ('Embarcadero', 'Wharf'): 6,
        ('Presidio', 'Richmond'): 7,
        ('Presidio', 'Wharf'): 19,
        ('Richmond', 'Wharf'): 18,
        ('Wharf', 'Presidio'): 17,
        ('Wharf', 'Richmond'): 18,
        ('Richmond', 'Presidio'): 7
    }

    # Convert all times to minutes since 9:00 AM (540 minutes)
    arrival_time = 540  # 9:00 AM

    # Friends' availability windows
    betty_available = (615, 1290)  # 10:15 AM - 9:30 PM
    david_available = (780, 1215)  # 1:00 PM - 8:15 PM
    barbara_available = (555, 1215)  # 9:15 AM - 8:15 PM

    # Meeting durations (minutes)
    betty_duration = 45
    david_duration = 90
    barbara_duration = 120

    # Meeting constraints
    s.add(betty_start >= betty_available[0], betty_end <= betty_available[1])
    s.add(betty_end == betty_start + betty_duration)
    s.add(david_start >= david_available[0], david_end <= david_available[1])
    s.add(david_end == david_start + david_duration)
    s.add(barbara_start >= barbara_available[0], barbara_end <= barbara_available[1])
    s.add(barbara_end == barbara_start + barbara_duration)

    # Define meeting locations
    locations = {
        'betty': 'Presidio',
        'david': 'Richmond',
        'barbara': 'Wharf'
    }

    # Try all possible meeting orders (6 permutations)
    from itertools import permutations
    for order in permutations(['betty', 'david', 'barbara']):
        temp_solver = Solver()
        
        # Copy all constraints to temporary solver
        for c in s.assertions():
            temp_solver.add(c)
        
        # Add ordering constraints
        prev_location = 'Embarcadero'
        prev_end = arrival_time
        
        for i, friend in enumerate(order):
            start_var = globals()[f"{friend}_start"]
            end_var = globals()[f"{friend}_end"]
            current_loc = locations[friend]
            
            # Travel time from previous location
            travel = travel_times.get((prev_location, current_loc), 0)
            
            # Meeting must start after travel time from previous location
            temp_solver.add(start_var >= prev_end + travel)
            
            # Update for next iteration
            prev_location = current_loc
            prev_end = end_var
        
        # Check if this order works
        if temp_solver.check() == sat:
            m = temp_solver.model()
            
            # Convert times to readable format
            def to_time(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h}:{m:02d}"
            
            print("SOLUTION:")
            print(f"Meet Betty at Presidio from {to_time(m[betty_start].as_long())} to {to_time(m[betty_end].as_long())}")
            print(f"Meet David at Richmond from {to_time(m[david_start].as_long())} to {to_time(m[david_end].as_long())}")
            print(f"Meet Barbara at Wharf from {to_time(m[barbara_start].as_long())} to {to_time(m[barbara_end].as_long())}")
            return
    
    print("No feasible schedule found")

solve_scheduling()