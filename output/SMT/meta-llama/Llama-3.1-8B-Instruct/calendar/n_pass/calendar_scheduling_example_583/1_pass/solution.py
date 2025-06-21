from z3 import *

def schedule_meeting(schedules, meeting_duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    days = ['Monday']
    start_times = [9]  # 9:00
    end_times = [17]  # 17:00
    time_slots = [(start, end) for start in start_times for end in [start + i for i in range(1, 8) if start + i <= end_times[0]]]

    # Add the constraints
    for person, schedule in schedules.items():
        for day, time_slots in schedule.items():
            for start, end in time_slots:
                for slot in time_slots:
                    if slot[0] < end and slot[1] > start:
                        solver.assert(Not(And(start <= slot[0], slot[1] <= end)))

    # Define the meeting time variables
    meeting_day = Int('meeting_day')
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add the constraints for the meeting time
    solver.assert(meeting_day == 0)  # Only one day to meet
    solver.assert(meeting_start >= 9)  # Start time should be after 9:00
    solver.assert(meeting_end <= 17)  # End time should be before 17:00
    solver.assert(meeting_end - meeting_start == meeting_duration)  # Meeting duration is half an hour
    solver.assert(ForAll([meeting_start, meeting_end], Implies(And(meeting_start >= 9, meeting_start + meeting_duration <= 17), Not(Any([person], And(meeting_start >= schedules[person]['Monday'][0][0], meeting_end <= schedules[person]['Monday'][-1][1]))))))

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        meeting_day_value = model.evaluate(meeting_day).as_long()
        meeting_start_value = model.evaluate(meeting_start).as_long()
        meeting_end_value = model.evaluate(meeting_end).as_long()

        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: {days[meeting_day_value]}")
        print(f"Start Time: {meeting_start_value:02d}:00")
        print(f"End Time: {meeting_end_value:02d}:00")
    else:
        print("No solution exists")

# Example usage
schedules = {
    'Lisa': {
        'Monday': [(9, 9, 30), (10, 30, 11, 0), (14, 0, 16, 0)]
    },
    'Anthony': {
        'Monday': [(9, 9, 30), (11, 0, 11, 30), (12, 30, 13, 30), (14, 0, 15, 0), (15, 30, 16, 0), (16, 30, 17, 0)]
    }
}

meeting_duration = 30  # Half an hour
schedule_meeting(schedules, meeting_duration)