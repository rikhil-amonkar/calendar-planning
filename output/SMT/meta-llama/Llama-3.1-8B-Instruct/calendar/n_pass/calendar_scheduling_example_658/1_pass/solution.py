from z3 import *

def schedule_meeting(shirley_schedule, albert_schedule, meeting_duration, day, preference=None):
    # Define the time slots for the day
    time_slots = []
    for hour in range(9, 17):
        for minute in range(0, 60, 30):
            start_time = f"{hour:02d}:{minute:02d}"
            end_time = f"{hour:02d}:{minute+30:02d}"
            time_slots.append((start_time, end_time))

    # Define the variables
    day_var = Int(day)
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')

    # Define the constraints
    constraints = []
    for time_slot in time_slots:
        start_time, end_time = time_slot
        if (day_var == 0 and (start_time, end_time) not in shirley_schedule) or \
           (day_var == 1 and (start_time, end_time) not in shirley_schedule) or \
           (day_var == 0 and (start_time, end_time) not in albert_schedule) or \
           (day_var == 1 and (start_time, end_time) in albert_schedule):
            continue
        constraints.append(And(start_time_var >= start_time, start_time_var <= end_time,
                              end_time_var >= start_time_var, end_time_var <= end_time_var + meeting_duration))

    if preference is not None:
        for time_slot in time_slots:
            start_time, end_time = time_slot
            if (day_var == 1 and start_time >= "10:30" and (start_time, end_time) not in shirley_schedule):
                constraints.append(Not(start_time_var >= start_time and start_time_var <= end_time))

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    solver.add(day_var >= 0)
    solver.add(day_var <= 1)
    solver.add(start_time_var >= "09:00")
    solver.add(start_time_var <= "16:30")
    solver.add(end_time_var >= start_time_var)
    solver.add(end_time_var <= start_time_var + meeting_duration)
    result = solver.check()

    # Print the solution
    if result == sat:
        model = solver.model()
        day = model[day_var].as_long()
        start_time = model[start_time_var].as_string()
        end_time = model[end_time_var].as_string()
        print(f"SOLUTION:")
        print(f"Day: {['Monday', 'Tuesday'][day]}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found.")

# Example usage:
shirley_schedule = [("10:30", "11:00"), ("12:00", "12:30"), ("16:00", "16:30"), ("09:30", "10:00")]
albert_schedule = [("09:00", "17:00"), ("09:30", "11:00"), ("11:30", "12:30"), ("13:00", "16:00"), ("16:30", "17:00")]
meeting_duration = 30
day = 0  # 0 for Monday, 1 for Tuesday
preference = True

schedule_meeting(shirley_schedule, albert_schedule, meeting_duration, day, preference)