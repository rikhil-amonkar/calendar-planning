from z3 import *

# Define the time intervals
time_intervals = {
    "Monday": [(0, 8*60), (8*60, 9*60), (9*60, 10*60), (10*60, 11*60), (11*60, 12*60), 
               (12*60, 13*60), (13*60, 14*60), (14*60, 15*60), (15*60, 16*60), (16*60, 17*60), 
               (17*60, 24*60)],
    "Tuesday": [(0, 8*60), (8*60, 9*60), (9*60, 10*60), (10*60, 11*60), (11*60, 12*60), 
                (12*60, 13*60), (13*60, 14*60), (14*60, 15*60), (15*60, 16*60), (16*60, 17*60), 
                (17*60, 24*60)],
    "Wednesday": [(0, 8*60), (8*60, 9*60), (9*60, 10*60), (10*60, 11*60), (11*60, 12*60), 
                  (12*60, 13*60), (13*60, 14*60), (14*60, 15*60), (15*60, 16*60), (16*60, 17*60), 
                  (17*60, 24*60)],
}

# Define the busy intervals for each person
busy_intervals = {
    "Joshua": {
        "Monday": [(15*60, 15*60+30)],
        "Tuesday": [(11*60+30, 12*60), (13*60, 13*60+30), (14*60+30, 15*60)],
        "Wednesday": [],
    },
    "Joyce": {
        "Monday": [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60+30), (13*60, 15*60), (15*60+30, 17*60)],
        "Tuesday": [(9*60, 17*60)],
        "Wednesday": [(9*60, 9*60+30), (10*60, 11*60), (12*60+30, 15*60+30), (16*60, 16*60+30)],
    }
}

# Create the solver
s = Solver()

# Create the variables
day = Int('day')
start_time = Int('start_time')

# Add the constraints
s.add(day >= 0)
s.add(day <= 2)  # 0: Monday, 1: Tuesday, 2: Wednesday
s.add(start_time >= 9*60)  # start time should be after 9:00
s.add(start_time <= 16*60)  # start time should be before 17:00
s.add(start_time + 30 <= 17*60)  # end time should be before 17:00

# Joyce would rather not meet on Monday before 12:00
s.add(Or(day!= 0, start_time >= 12*60))

# Joyce would rather meet on Wednesday
s.add(day == 2)

# Add the constraints for the busy intervals
for person, intervals in busy_intervals.items():
    for i, interval in enumerate(intervals):
        s.add(Or(day!= list(busy_intervals[person].keys()).index(interval), 
                  start_time < busy_intervals[person][interval][0], 
                  start_time + 30 > busy_intervals[person][interval][1]))

# Check the solution
if s.check() == sat:
    model = s.model()
    day_index = model[day].as_long()
    start_time_minutes = model[start_time].as_long()
    day_name = list(time_intervals.keys())[day_index]
    print(f"Meeting can be scheduled on {day_name} at {start_time_minutes//60}:{start_time_minutes%60:02d} for 30 minutes.")
else:
    print("No solution found.")