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

# Define the start and end times for meetings with Jessica and Carol
jessica_start_time = Int('jessica_start_time')
jessica_end_time = Int('jessica_end_time')
carol_start_time = Int('carol_start_time')
carol_end_time = Int('carol_end_time')

# Add constraints for Jessica's meeting
solver.add(jessica_start_time >= jessica_start)
solver.add(jessica_end_time <= jessica_end)
solver.add(jessica_end_time - jessica_start_time >= jessica_min_duration)

# Add constraints for Carol's meeting
solver.add(carol_start_time >= carol_start)
solver.add(carol_end_time <= carol_end)
solver.add(carol_end_time - carol_start_time >= carol_min_duration)

# Define the start time at Richmond District
start_time_richmond = time_in_minutes(9, 0)  # 9:00AM

# Define the travel constraints
# Travel from Richmond District to Pacific Heights for Jessica's meeting
solver.add(jessica_start_time >= start_time_richmond + travel_times[('Richmond District', 'Pacific Heights')])

# Travel from Richmond District to Marina District for Carol's meeting
solver.add(carol_start_time >= start_time_richmond + travel_times[('Richmond District', 'Marina District')])

# Travel from Pacific Heights to Marina District if both meetings are scheduled
solver.add(Implies(And(jessica_end_time <= carol_start_time, carol_start_time - jessica_end_time >= travel_times[('Pacific Heights', 'Marina District')]), True))

# Travel from Marina District to Pacific Heights if both meetings are scheduled
solver.add(Implies(And(carol_end_time <= jessica_start_time, jessica_start_time - carol_end_time >= travel_times[('Marina District', 'Pacific Heights')]), True))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    jessica_start_time_val = model[jessica_start_time].as_long()
    jessica_end_time_val = model[jessica_end_time].as_long()
    carol_start_time_val = model[carol_start_time].as_long()
    carol_end_time_val = model[carol_end_time].as_long()

    # Convert the times back to HH:MM format
    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = []
    if jessica_start_time_val < jessica_end_time_val:
        itinerary.append({
            "action": "meet",
            "person": "Jessica",
            "start_time": format_time(jessica_start_time_val),
            "end_time": format_time(jessica_end_time_val)
        })
    if carol_start_time_val < carol_end_time_val:
        itinerary.append({
            "action": "meet",
            "person": "Carol",
            "start_time": format_time(carol_start_time_val),
            "end_time": format_time(carol_end_time_val)
        })

    print({"itinerary": itinerary})
else:
    print("No solution found")