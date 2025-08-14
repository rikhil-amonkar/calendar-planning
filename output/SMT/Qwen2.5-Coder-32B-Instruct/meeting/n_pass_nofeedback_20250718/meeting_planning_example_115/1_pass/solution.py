from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Marina District'): 6,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7
}

# Define the availability of Jessica and Carol
jessica_start = time_in_minutes(15, 30)  # 3:30PM
jessica_end = time_in_minutes(16, 45)    # 4:45PM
carol_start = time_in_minutes(11, 30)    # 11:30AM
carol_end = time_in_minutes(15, 0)       # 3:00PM

# Define the minimum meeting durations
jessica_min_duration = 45
carol_min_duration = 60

# Define the solver
solver = Solver()

# Define the variables for the start and end times of meetings
jessica_start_meeting = Int('jessica_start_meeting')
jessica_end_meeting = Int('jessica_end_meeting')
carol_start_meeting = Int('carol_start_meeting')
carol_end_meeting = Int('carol_end_meeting')

# Add constraints for Jessica's meeting
solver.add(jessica_start_meeting >= jessica_start)
solver.add(jessica_end_meeting <= jessica_end)
solver.add(jessica_end_meeting - jessica_start_meeting >= jessica_min_duration)

# Add constraints for Carol's meeting
solver.add(carol_start_meeting >= carol_start)
solver.add(carol_end_meeting <= carol_end)
solver.add(carol_end_meeting - carol_start_meeting >= carol_min_duration)

# Define the variables for the current location and time
current_location = String('current_location')
current_time = Int('current_time')

# Initial conditions
solver.add(current_location == 'Richmond District')
solver.add(current_time == 0)  # 9:00AM

# Define the transitions
transitions = [
    (current_location == 'Richmond District', current_location == 'Pacific Heights', current_time + travel_times[('Richmond District', 'Pacific Heights')]),
    (current_location == 'Richmond District', current_location == 'Marina District', current_time + travel_times[('Richmond District', 'Marina District')]),
    (current_location == 'Pacific Heights', current_location == 'Richmond District', current_time + travel_times[('Pacific Heights', 'Richmond District')]),
    (current_location == 'Pacific Heights', current_location == 'Marina District', current_time + travel_times[('Pacific Heights', 'Marina District')]),
    (current_location == 'Marina District', current_location == 'Richmond District', current_time + travel_times[('Marina District', 'Richmond District')]),
    (current_location == 'Marina District', current_location == 'Pacific Heights', current_time + travel_times[('Marina District', 'Pacific Heights')])
]

# Add constraints for transitions
for (from_loc, to_loc, new_time) in transitions:
    solver.add(Or(current_location != from_loc, current_location == to_loc, current_time == new_time))

# Add constraints for meeting times
solver.add(Or(current_location != 'Pacific Heights', current_time >= jessica_start_meeting, current_time <= jessica_end_meeting))
solver.add(Or(current_location != 'Marina District', current_time >= carol_start_meeting, current_time <= carol_end_meeting))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    jessica_start_meeting_time = model[jessica_start_meeting].as_long()
    jessica_end_meeting_time = model[jessica_end_meeting].as_long()
    carol_start_meeting_time = model[carol_start_meeting].as_long()
    carol_end_meeting_time = model[carol_end_meeting].as_long()

    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = []
    if jessica_start_meeting_time != jessica_end_meeting_time:
        itinerary.append({
            "action": "meet",
            "person": "Jessica",
            "start_time": format_time(jessica_start_meeting_time),
            "end_time": format_time(jessica_end_meeting_time)
        })
    if carol_start_meeting_time != carol_end_meeting_time:
        itinerary.append({
            "action": "meet",
            "person": "Carol",
            "start_time": format_time(carol_start_meeting_time),
            "end_time": format_time(carol_end_meeting_time)
        })

    print({"itinerary": itinerary})
else:
    print("No solution found")