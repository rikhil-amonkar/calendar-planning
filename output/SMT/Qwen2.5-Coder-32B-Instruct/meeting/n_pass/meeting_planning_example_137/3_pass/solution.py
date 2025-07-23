from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the constraints
def solve_schedule():
    # Create a solver instance
    solver = Solver()

    # Define the start and end times for meetings with Kenneth and Barbara
    k_start = Int('k_start')
    k_end = Int('k_end')
    b_start = Int('b_start')
    b_end = Int('b_end')

    # Constraints for Kenneth's availability
    solver.add(k_start >= 5)  # Start time after traveling to Chinatown
    solver.add(k_end <= 360)  # End time before 6:00 PM
    solver.add(k_end - k_start >= 90)  # Minimum 90 minutes

    # Constraints for Barbara's availability
    solver.add(b_start >= 23)  # Start time after traveling to Golden Gate Park
    solver.add(b_end <= 600)  # End time before 10:00 PM
    solver.add(b_end - b_start >= 45)  # Minimum 45 minutes

    # Constraints for no overlapping meetings
    solver.add(k_start >= b_end + 23)  # Kenneth's meeting starts after Barbara's meeting ends and travel time
    solver.add(b_start >= k_end + 23)  # Barbara's meeting starts after Kenneth's meeting ends and travel time

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        k_start_time = model[k_start].as_long()
        k_end_time = model[k_end].as_long()
        b_start_time = model[b_start].as_long()
        b_end_time = model[b_end].as_long()

        # Convert times back to HH:MM format
        def format_time(minutes):
            hours = 9 + minutes // 60
            minutes = minutes % 60
            return f"{hours:02}:{minutes:02}"

        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": format_time(b_start_time), "end_time": format_time(b_end_time)},
            {"action": "meet", "person": "Kenneth", "start_time": format_time(k_start_time), "end_time": format_time(k_end_time)}
        ]

        return {"itinerary": itinerary}
    else:
        return "No solution found"

# Get the solution
solution = solve_schedule()
print(solution)