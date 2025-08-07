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
    solver.add(k_start >= time_in_minutes(12, 0))
    solver.add(k_end <= time_in_minutes(15, 0))
    solver.add(k_end - k_start >= 90)  # Minimum 90 minutes

    # Constraints for Barbara's availability
    solver.add(b_start >= time_in_minutes(8, 15))
    solver.add(b_end <= time_in_minutes(19, 0))
    solver.add(b_end - b_start >= 45)  # Minimum 45 minutes

    # Travel times in minutes
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23
    }

    # Define the start time at Financial District
    start_time = time_in_minutes(9, 0)

    # Define two possible sequences of meetings
    # Sequence 1: Barbara -> Kenneth
    b_start_1 = Int('b_start_1')
    b_end_1 = Int('b_end_1')
    k_start_1 = Int('k_start_1')
    k_end_1 = Int('k_end_1')

    # Constraints for Barbara in sequence 1
    solver.add(b_start_1 >= start_time + travel_times[('Financial District', 'Golden Gate Park')])
    solver.add(b_end_1 <= time_in_minutes(19, 0))
    solver.add(b_end_1 - b_start_1 >= 45)  # Minimum 45 minutes

    # Constraints for Kenneth in sequence 1
    solver.add(k_start_1 >= b_end_1 + travel_times[('Golden Gate Park', 'Chinatown')])
    solver.add(k_end_1 <= time_in_minutes(15, 0))
    solver.add(k_end_1 - k_start_1 >= 90)  # Minimum 90 minutes

    # Sequence 2: Kenneth -> Barbara
    k_start_2 = Int('k_start_2')
    k_end_2 = Int('k_end_2')
    b_start_2 = Int('b_start_2')
    b_end_2 = Int('b_end_2')

    # Constraints for Kenneth in sequence 2
    solver.add(k_start_2 >= start_time + travel_times[('Financial District', 'Chinatown')])
    solver.add(k_end_2 <= time_in_minutes(15, 0))
    solver.add(k_end_2 - k_start_2 >= 90)  # Minimum 90 minutes

    # Constraints for Barbara in sequence 2
    solver.add(b_start_2 >= k_end_2 + travel_times[('Chinatown', 'Golden Gate Park')])
    solver.add(b_end_2 <= time_in_minutes(19, 0))
    solver.add(b_end_2 - b_start_2 >= 45)  # Minimum 45 minutes

    # Add a boolean variable to choose between the two sequences
    seq1 = Bool('seq1')
    seq2 = Bool('seq2')
    solver.add(seq1 == Not(seq2))

    # Add constraints for sequence 1
    solver.add(Implies(seq1, And(
        b_start_1 == b_start,
        b_end_1 == b_end,
        k_start_1 == k_start,
        k_end_1 == k_end
    )))

    # Add constraints for sequence 2
    solver.add(Implies(seq2, And(
        k_start_2 == k_start,
        k_end_2 == k_end,
        b_start_2 == b_start,
        b_end_2 == b_end
    )))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        k_start_time = model[k_start].as_long()
        k_end_time = model[k_end].as_long()
        b_start_time = model[b_start].as_long()
        b_end_time = model[b_end].as_long()

        # Convert times back to HH:MM format
        def format_time(minutes):
            hours = minutes // 60 + 9
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