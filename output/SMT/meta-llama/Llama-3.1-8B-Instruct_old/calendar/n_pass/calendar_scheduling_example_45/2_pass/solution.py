from z3 import *

def schedule_meeting(available_days, start_times, end_times, meeting_duration, preferences=None):
    # Create a Z3 solver
    solver = Solver()

    # Define the meeting duration in minutes
    meeting_duration_minutes = int(meeting_duration * 60)

    # Define the time slots for each day
    time_slots = []
    for day in available_days:
        for hour in range(9, 17):
            for minute in range(0, 60, 30):
                start_time = hour * 60 + minute
                end_time = start_time + meeting_duration_minutes
                if (day, start_time, end_time) not in time_slots:
                    time_slots.append((day, start_time, end_time))

    # Define the variables for each time slot
    time_slot_vars = []
    for i, (day, start_time, end_time) in enumerate(time_slots):
        var = Bool(f'time_slot_{i}')
        solver.add(var)
        time_slot_vars.append(var)

    # Define the constraints for each participant
    for participant in preferences:
        for time_slot in preferences[participant]:
            day, start_time, end_time = time_slot
            index = next((i for i, (d, s, e) in enumerate(time_slots) if d == day and s == start_time and e == end_time), None)
            if index is not None:
                solver.add(Not(time_slot_vars[index]))
            else:
                print(f"Warning: Time slot {time_slot} not found in time slots.")

    # Define the constraints for the meeting duration
    for i in range(len(time_slots) - 1):
        solver.add(Or(time_slot_vars[i], Not(time_slot_vars[i+1])))

    # Solve the problem
    solver.check()

    # Get the solution
    model = solver.model()

    # Find the first time slot that is True
    for i, var in enumerate(time_slot_vars):
        if model.evaluate(var).as_bool():
            day, start_time, end_time = time_slots[i]
            break

    # Print the solution
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {start_time // 60:02d}:{start_time % 60:02d}')
    print(f'End Time: {(start_time + meeting_duration_minutes) // 60:02d}:{(start_time + meeting_duration_minutes) % 60:02d}')

# Example usage
available_days = ['Monday']
start_times = [9 * 60 + 0, 9 * 60 + 0, 9 * 60 + 0]
end_times = [17 * 60 + 0, 17 * 60 + 0, 17 * 60 + 0]
meeting_duration = 0.5
preferences = {
    'Andrew': [],
    'Grace': [],
    'Samuel': [(9 * 60 + 0, 9 * 60 + 30), (11 * 60 + 30, 11 * 60 + 60), (13 * 60 + 0, 13 * 60 + 30), (14 * 60 + 0, 16 * 60 + 0), (16 * 60 + 30, 17 * 60 + 0)]
}

schedule_meeting(available_days, start_times, end_times, meeting_duration, preferences)