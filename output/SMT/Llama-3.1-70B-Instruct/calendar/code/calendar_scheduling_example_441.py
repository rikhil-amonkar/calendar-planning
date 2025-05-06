from z3 import *

# Define the time intervals
time_intervals = {
    "Monday": [(0, 8*60), (8*60, 9*60), (9*60, 10*60), (10*60, 11*60), (11*60, 12*60), 
               (12*60, 13*60), (13*60, 14*60), (14*60, 15*60), (15*60, 16*60), (16*60, 17*60), 
               (17*60, 24*60)],
}

# Define the busy intervals for each person
busy_intervals = {
    "Joan": {
        "Monday": [(11*60+30, 12*60), (14*60+30, 15*60)],
    },
    "Megan": {
        "Monday": [(9*60, 10*60), (14*60, 14*60+30), (16*60, 16*60+30)],
    },
    "Austin": {
        "Monday": [],
    },
    "Betty": {
        "Monday": [(9*60+30, 10*60), (11*60+30, 12*60), (13*60+30, 14*60), (16*60, 16*60+30)],
    },
    "Judith": {
        "Monday": [(9*60, 11*60), (12*60, 13*60), (14*60, 15*60)],
    },
    "Terry": {
        "Monday": [(9*60+30, 10*60), (11*60+30, 12*60+30), (13*60, 14*60), (15*60, 15*60+30), (16*60, 17*60)],
    },
    "Kathryn": {
        "Monday": [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 13*60), (14*60, 16*60), (16*60+30, 17*60)],
    }
}

# Create the solver
s = Solver()

# Create the variables
start_time = Int('start_time')

# Add the constraints
s.add(start_time >= 9*60)  # start time should be after 9:00
s.add(start_time <= 16*60)  # start time should be before 17:00
s.add(start_time + 30 <= 17*60)  # end time should be before 17:00

# Add the constraints for the busy intervals
for person, intervals in busy_intervals.items():
    for i, interval in enumerate(intervals["Monday"]):
        s.add(Or(start_time < busy_intervals[person]["Monday"][i][0], 
                  start_time + 30 > busy_intervals[person]["Monday"][i][1]))

# Check the solution
if s.check() == sat:
    model = s.model()
    start_time_minutes = model[start_time].as_long()
    print(f"Meeting can be scheduled on Monday at {start_time_minutes//60}:{start_time_minutes%60:02d} for 30 minutes.")
else:
    print("No solution found.")