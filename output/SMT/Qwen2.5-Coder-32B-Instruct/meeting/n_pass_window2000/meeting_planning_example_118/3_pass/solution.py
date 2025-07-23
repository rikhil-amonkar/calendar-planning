from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the constraints
start_time = time_in_minutes(9, 0)  # 9:00AM
richard_start = time_in_minutes(8, 45)  # 8:45AM
richard_end = time_in_minutes(13, 0)  # 1:00PM
charles_start = time_in_minutes(9, 45)  # 9:45AM
charles_end = time_in_minutes(13, 0)  # 1:00PM

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

# Define the travel times as constraints
# Option 1: Bayview -> Union Square -> Presidio
# Travel from Bayview to Union Square
union_square_arrival_1 = start_time + travel_times[('Bayview', 'Union Square')]
# Richard meeting
solver.add(richard_meeting_start >= union_square_arrival_1)
# Travel from Union Square to Presidio
presidio_arrival_1 = richard_meeting_end + travel_times[('Union Square', 'Presidio')]
# Charles meeting
solver.add(charles_meeting_start >= presidio_arrival_1)

# Option 2: Bayview -> Presidio -> Union Square
# Travel from Bayview to Presidio
presidio_arrival_2 = start_time + travel_times[('Bayview', 'Presidio')]
# Charles meeting
solver.add(charles_meeting_start >= presidio_arrival_2)
# Travel from Presidio to Union Square
union_square_arrival_2 = charles_meeting_end + travel_times[('Presidio', 'Union Square')]
# Richard meeting
solver.add(richard_meeting_start >= union_square_arrival_2)

# Ensure that the meetings do not overlap
solver.add(Or(richard_meeting_end <= charles_meeting_start, charles_meeting_end <= richard_meeting_start))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    richard_meeting_start_time = model[richard_meeting_start].as_long()
    richard_meeting_end_time = model[richard_meeting_end].as_long()
    charles_meeting_start_time = model[charles_meeting_start].as_long()
    charles_meeting_end_time = model[charles_meeting_end].as_long()

    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Richard", "start_time": format_time(richard_meeting_start_time), "end_time": format_time(richard_meeting_end_time)},
        {"action": "meet", "person": "Charles", "start_time": format_time(charles_meeting_start_time), "end_time": format_time(charles_meeting_end_time)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")