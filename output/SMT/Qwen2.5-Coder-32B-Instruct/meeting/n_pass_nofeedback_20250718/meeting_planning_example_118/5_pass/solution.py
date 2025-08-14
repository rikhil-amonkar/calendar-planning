from z3 import *

# Define the time in minutes from 9:00 AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the constraints
start_time = time_in_minutes(9, 0)  # 9:00 AM
richard_start = time_in_minutes(8, 45)  # 8:45 AM
richard_end = time_in_minutes(13, 0)  # 1:00 PM
charles_start = time_in_minutes(9, 45)  # 9:45 AM
charles_end = time_in_minutes(13, 0)  # 1:00 PM

# Define the travel times in minutes
travel_times = {
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Union Square'): 22
}

# Create the solver
solver = Solver()

# Define the variables for the start and end times of meetings
richard_meeting_start = Int('richard_meeting_start')
richard_meeting_end = Int('richard_meeting_end')
charles_meeting_start = Int('charles_meeting_start')
charles_meeting_end = Int('charles_meeting_end')

# Add constraints for Richard's meeting
solver.add(richard_meeting_start >= richard_start)
solver.add(richard_meeting_end <= richard_end)
solver.add(richard_meeting_end - richard_meeting_start >= 120)

# Add constraints for Charles's meeting
solver.add(charles_meeting_start >= charles_start)
solver.add(charles_meeting_end <= charles_end)
solver.add(charles_meeting_end - charles_meeting_start >= 120)

# Define the sequences explicitly
# Sequence 1: Bayview -> Union Square -> Presidio
# Start at Bayview, travel to Union Square, meet Richard, travel to Presidio, meet Charles
sequence1 = And(
    richard_meeting_start >= start_time + travel_times[('Bayview', 'Union Square')],
    richard_meeting_end + travel_times[('Union Square', 'Presidio')] <= charles_meeting_start,
    charles_meeting_end <= richard_end
)

# Sequence 2: Bayview -> Presidio -> Union Square
# Start at Bayview, travel to Presidio, meet Charles, travel to Union Square, meet Richard
sequence2 = And(
    charles_meeting_start >= start_time + travel_times[('Bayview', 'Presidio')],
    charles_meeting_end + travel_times[('Presidio', 'Union Square')] <= richard_meeting_start,
    richard_meeting_end <= charles_end
)

# Add the sequences to the solver
solver.add(Or(sequence1, sequence2))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    richard_meeting_start_val = model[richard_meeting_start].as_long()
    richard_meeting_end_val = model[richard_meeting_end].as_long()
    charles_meeting_start_val = model[charles_meeting_start].as_long()
    charles_meeting_end_val = model[charles_meeting_end].as_long()

    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Richard", "start_time": format_time(richard_meeting_start_val), "end_time": format_time(richard_meeting_end_val)},
        {"action": "meet", "person": "Charles", "start_time": format_time(charles_meeting_start_val), "end_time": format_time(charles_meeting_end_val)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")