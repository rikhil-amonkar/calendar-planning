from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Variables for meeting Emily
    emily_start = Int('emily_start')  # in minutes from 9:00 AM
    emily_end = Int('emily_end')

    # Variables for meeting Margaret
    margaret_start = Int('margaret_start')  # in minutes from 9:00 AM
    margaret_end = Int('margaret_end')

    # Convert time constraints to minutes from 9:00 AM
    # Emily's availability: 4:00 PM (16:00) to 5:15 PM (17:15) is 420 to 495 minutes from 9:00 AM
    emily_min_start = 16 * 60 - 9 * 60  # 420 minutes (4:00 PM)
    emily_max_end = 17 * 60 + 15 - 9 * 60  # 495 minutes (5:15 PM)

    # Margaret's availability: 7:00 PM (19:00) to 9:00 PM (21:00) is 600 to 720 minutes from 9:00 AM
    margaret_min_start = 19 * 60 - 9 * 60  # 600 minutes (7:00 PM)
    margaret_max_end = 21 * 60 - 9 * 60  # 720 minutes (9:00 PM)

    # Meeting durations
    emily_duration = 45
    margaret_duration = 120

    # Constraints for Emily's meeting
    s.add(emily_start >= emily_min_start)
    s.add(emily_end <= emily_max_end)
    s.add(emily_end == emily_start + emily_duration)

    # Constraints for Margaret's meeting
    s.add(margaret_start >= margaret_min_start)
    s.add(margaret_end <= margaret_max_end)
    s.add(margaret_end == margaret_start + margaret_duration)

    # Travel times in minutes
    # From North Beach to Union Square: 7 minutes
    # From North Beach to Russian Hill: 4 minutes
    # From Union Square to Russian Hill: 13 minutes
    # From Russian Hill to Union Square: 11 minutes
    # From Russian Hill to North Beach: 5 minutes
    # From Union Square to North Beach: 10 minutes

    # We start at North Beach at 0 minutes (9:00 AM)
    # Possible sequences:
    # Option 1: Meet Emily first, then Margaret
    #   - Travel from North Beach to Union Square: 7 minutes
    #   - Then, travel from Union Square to Russian Hill: 13 minutes
    #   - So, emily_start >= 7 (since we start at 0)
    #   - margaret_start >= emily_end + 13
    # Option 2: Meet Margaret first, then Emily
    #   - Travel from North Beach to Russian Hill: 4 minutes
    #   - Then, travel from Russian Hill to Union Square: 11 minutes
    #   - So, margaret_start >= 4
    #   - emily_start >= margaret_end + 11
    # However, Emily's meeting must be before Margaret's because Margaret's meeting starts at 7:00 PM, which is after Emily's window.
    # So, Option 1 is the only feasible sequence.

    # Add travel constraints for Option 1: Emily first, then Margaret
    s.add(emily_start >= 7)  # travel from North Beach to Union Square
    s.add(margaret_start >= emily_end + 13)  # travel from Union Square to Russian Hill

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Extract the values
        emily_start_val = m[emily_start].as_long()
        emily_end_val = m[emily_end].as_long()
        margaret_start_val = m[margaret_start].as_long()
        margaret_end_val = m[margaret_end].as_long()

        # Convert minutes back to HH:MM format from 9:00 AM
        def minutes_to_time(minutes):
            total_minutes = 9 * 60 + minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        emily_start_time = minutes_to_time(emily_start_val)
        emily_end_time = minutes_to_time(emily_end_val)
        margaret_start_time = minutes_to_time(margaret_start_val)
        margaret_end_time = minutes_to_time(margaret_end_val)

        # Create the itinerary
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": emily_start_time, "end_time": emily_end_time},
            {"action": "meet", "person": "Margaret", "start_time": margaret_start_time, "end_time": margaret_end_time}
        ]

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))