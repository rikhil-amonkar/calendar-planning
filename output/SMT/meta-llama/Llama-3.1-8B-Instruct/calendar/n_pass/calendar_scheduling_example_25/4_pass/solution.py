from z3 import *

def schedule_meeting():
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    end_time = Int('end_time')
    meeting_duration = 60  # in minutes

    # Define the constraints
    constraints = [
        And(start_time >= 9*60, start_time <= 17*60),  # Between 9:00 and 17:00
        And(end_time >= 9*60, end_time <= 17*60),  # Between 9:00 and 17:00
        And(start_time + meeting_duration <= 17*60),  # End time is within the day
        start_time!= 9*60,  # Start time is not 9:00
        start_time!= 17*60,  # Start time is not 17:00
        end_time!= 9*60,  # End time is not 9:00
        end_time!= 17*60,  # End time is not 17:00
    ]

    # Define the busy times for each person
    anthony_busy_times = [9*60 + 30, 12*60, 16*60 + 30]
    pamela_busy_times = [9*60 + 30, 16*60 + 30]
    zachary_busy_times = [9*60, 12*60, 13*60, 14*60 + 30, 16*60]
    pamela_preferred_end_time = 14*60 + 30

    # Add constraints based on busy times
    constraints.append(
        Or(
            start_time + meeting_duration > anthony_busy_times[0],
            start_time < anthony_busy_times[0],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > anthony_busy_times[1],
            start_time < anthony_busy_times[1],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > anthony_busy_times[2],
            start_time < anthony_busy_times[2],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > pamela_busy_times[0],
            start_time < pamela_busy_times[0],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > pamela_busy_times[1],
            start_time < pamela_busy_times[1],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > zachary_busy_times[0],
            start_time < zachary_busy_times[0],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > zachary_busy_times[1],
            start_time < zachary_busy_times[1],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > zachary_busy_times[2],
            start_time < zachary_busy_times[2],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > zachary_busy_times[3],
            start_time < zachary_busy_times[3],
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration > zachary_busy_times[4],
            start_time < zachary_busy_times[4],
        )
    )
    constraints.append(start_time + meeting_duration <= pamela_preferred_end_time)

    # Add constraints to avoid conflicts with unavailable time slots
    constraints.append(
        Or(
            start_time + meeting_duration <= 10,
            start_time >= 10,
        )
    )
    constraints.append(
        Or(
            start_time + meeting_duration <= 12*60,
            start_time >= 13*60,
        )
    )

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = start_time_value + meeting_duration
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}"
    else:
        return "No solution found"

print(schedule_meeting())