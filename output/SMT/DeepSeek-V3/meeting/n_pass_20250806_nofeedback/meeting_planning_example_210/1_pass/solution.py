from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the meeting start and end times for each friend
    emily_start = Int('emily_start')  # in minutes from 9:00 AM
    emily_end = Int('emily_end')
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')

    # Convert friend availability windows to minutes since 9:00 AM
    # Emily: 4:15 PM to 9:00 PM (15:15 to 21:00 in 24-hour format)
    emily_available_start = (15 * 60 + 15) - (9 * 60)  # 6*60 + 15 = 375 minutes
    emily_available_end = (21 * 60) - (9 * 60)  # 12*60 = 720 minutes
    # Joseph: 5:15 PM to 10:00 PM (17:15 to 22:00)
    joseph_available_start = (17 * 60 + 15) - (9 * 60)  # 8*60 + 15 = 495 minutes
    joseph_available_end = (22 * 60) - (9 * 60)  # 13*60 = 780 minutes
    # Melissa: 3:45 PM to 9:45 PM (15:45 to 21:45)
    melissa_available_start = (15 * 60 + 45) - (9 * 60)  # 6*60 + 45 = 405 minutes
    melissa_available_end = (21 * 60 + 45) - (9 * 60)  # 12*60 + 45 = 765 minutes

    # Add constraints for meeting durations
    s.add(emily_end - emily_start >= 105)  # Emily: 105 minutes
    s.add(joseph_end - joseph_start >= 120)  # Joseph: 120 minutes
    s.add(melissa_end - melissa_start >= 75)  # Melissa: 75 minutes

    # Add constraints for meeting within availability windows
    s.add(emily_start >= emily_available_start)
    s.add(emily_end <= emily_available_end)
    s.add(joseph_start >= joseph_available_start)
    s.add(joseph_end <= joseph_available_end)
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)

    # Define travel times (in minutes)
    travel = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
    }

    # We need to model the sequence of meetings and travel times.
    # Since we start at Fisherman's Wharf at 0 minutes (9:00 AM), we can choose the order of meetings.
    # Let's assume the order is Melissa, Emily, Joseph (or other permutations).
    # We'll try all possible permutations and pick the feasible one.

    # We'll define variables for the order of meetings.
    # For simplicity, let's assume the order is Melissa -> Emily -> Joseph.
    # Then, the constraints are:
    # 1. Travel from Fisherman's Wharf to Financial District (Melissa's location): 11 minutes.
    #    So melissa_start >= 11.
    # 2. After Melissa, travel to Emily's location (Presidio).
    #    Travel from Financial District to Presidio: 22 minutes.
    #    So emily_start >= melissa_end + 22.
    # 3. After Emily, travel to Joseph's location (Richmond District).
    #    Travel from Presidio to Richmond District: 7 minutes.
    #    So joseph_start >= emily_end + 7.

    s.add(melissa_start >= 11)  # Travel from Fisherman's Wharf to Financial District
    s.add(emily_start >= melissa_end + 22)  # Travel from Financial District to Presidio
    s.add(joseph_start >= emily_end + 7)  # Travel from Presidio to Richmond District

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the meeting times
        emily_s = model[emily_start].as_long()
        emily_e = model[emily_end].as_long()
        joseph_s = model[joseph_start].as_long()
        joseph_e = model[joseph_end].as_long()
        melissa_s = model[melissa_start].as_long()
        melissa_e = model[melissa_end].as_long()

        # Convert minutes since 9:00 AM to HH:MM format
        def to_time_str(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": to_time_str(melissa_s), "end_time": to_time_str(melissa_e)},
            {"action": "meet", "person": "Emily", "start_time": to_time_str(emily_s), "end_time": to_time_str(emily_e)},
            {"action": "meet", "person": "Joseph", "start_time": to_time_str(joseph_s), "end_time": to_time_str(joseph_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))