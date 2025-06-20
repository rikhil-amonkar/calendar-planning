from z3 import *

def schedule_meeting(start_time, end_time, james_schedule, john_schedule):
    # Create a solver
    s = Solver()

    # Define the variables
    day = Int('day')
    james_start = Int('james_start')
    john_start = Int('john_start')

    # Define the constraints
    s.add(day == 0)  # day is 0 for Monday
    s.add(And(start_time <= james_start, james_start <= end_time))
    s.add(And(start_time <= john_start, john_start <= end_time))
    for james_block in james_schedule:
        s.add(Or(james_start < james_block[0], james_start >= james_block[1]))
    for john_block in john_schedule:
        s.add(Or(john_start < john_block[0], john_start >= john_block[1]))
    s.add(james_start >= 9 * 60)  # start time is after 9:00
    s.add(james_start <= 16 * 60)  # start time is before 16:00 (to have 1 hour duration)
    s.add(john_start >= 9 * 60)  # start time is after 9:00
    s.add(john_start <= 16 * 60)  # start time is before 16:00
    s.add(james_start % 60 == 0)  # start time is on the hour
    s.add(john_start % 60 == 0)  # start time is on the hour
    s.add(james_start >= 10 * 60)  # start time is after 10:00
    s.add(james_start <= 15 * 60)  # start time is before 15:00
    s.add(john_start >= 10 * 60)  # start time is after 10:00
    s.add(john_start <= 15 * 60)  # start time is before 15:00

    # Check if there is a solution
    if s.check() == sat:
        # Get the solution
        model = s.model()
        james_start_val = model[james_start].as_long()
        john_start_val = model[john_start].as_long()
        # Calculate the start and end times
        start_time = james_start_val // 60
        end_time = (james_start_val // 60) + 1
        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time:02d}:00")
        print(f"End Time: {(start_time + 1):02d}:00")
    else:
        print("No solution found")

# Example usage
james_schedule = [(330, 360), (450, 480)]
john_schedule = [(570, 660), (600, 660), (720, 780), (450, 840)]
schedule_meeting(360, 420, james_schedule, john_schedule)