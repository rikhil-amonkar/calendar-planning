from z3 import *

def schedule_meeting(jack_schedule, charlotte_schedule, duration, preferences):
    # Create Z3 solver
    s = Solver()

    # Define variables
    day = [Bool('day_' + str(i)) for i in range(1, 8)]  # Monday to Sunday
    start_time = [Int('start_time_' + str(i)) for i in range(1, 8)]
    end_time = [start_time[i] + duration for i in range(7)]

    # Add constraints
    for i in range(7):
        s.add(day[i] == False)  # Initially, all days are False
        s.add(start_time[i] >= 9 * 60, start_time[i] <= 17 * 60)  # Start time must be between 9:00 and 17:00
        s.add(end_time[i] >= 9 * 60, end_time[i] <= 17 * 60)  # End time must be between 9:00 and 17:00

    # Add constraints based on existing schedules
    for i in range(7):
        for start, end in jack_schedule:
            s.add(day[i] == False)  # Jack is busy on this day
            s.add(Or(start_time[i] < start * 60, end_time[i] > end * 60))  # Jack is not busy at this time
        for start, end in charlotte_schedule:
            s.add(day[i] == False)  # Charlotte is busy on this day
            s.add(Or(start_time[i] < start * 60, end_time[i] > end * 60))  # Charlotte is not busy at this time

    # Add constraints based on preferences
    for i in range(7):
        s.add(day[i] == False)  # Initially, all days are False
        if i == 0:  # Jack wants to avoid meetings after 12:30 on Monday
            s.add(Or(start_time[i] < 12 * 60 + 30, end_time[i] < 12 * 60 + 30))

    # Find a solution
    s.add(day[0])  # Monday is the only day we care about
    s.add(Or(start_time[0] == 9 * 60 + 0, start_time[0] == 9 * 60 + 30, start_time[0] == 10 * 60 + 0, start_time[0] == 10 * 60 + 30, start_time[0] == 11 * 60 + 0, start_time[0] == 11 * 60 + 30, start_time[0] == 12 * 60 + 0, start_time[0] == 12 * 60 + 30, start_time[0] == 13 * 60 + 0, start_time[0] == 13 * 60 + 30, start_time[0] == 14 * 60 + 0, start_time[0] == 14 * 60 + 30, start_time[0] == 15 * 60 + 0, start_time[0] == 15 * 60 + 30, start_time[0] == 16 * 60 + 0, start_time[0] == 16 * 60 + 30))
    s.add(end_time[0] == start_time[0] + duration)  # Duration must be 30 minutes

    if s.check() == sat:
        model = s.model()
        day = model[day[0]].as_bool()
        start_time = model[start_time[0]].as_int()
        end_time = model[end_time[0]].as_int()
        return f"SOLUTION:\nDay: {'Monday' if day else 'Tuesday'}\nStart Time: {str(start_time // 60).zfill(2)}:{str(start_time % 60).zfill(2)}\nEnd Time: {str((start_time + duration) // 60).zfill(2)}:{str((start_time + duration) % 60).zfill(2)}"
    else:
        return "No solution found"

# Example usage
jack_schedule = [(9.5, 10.5), (10.5, 11.5), (12.5, 13.5), (14.5, 15.5), (15.5, 16.5)]
charlotte_schedule = [(9.5, 10.5), (10.5, 12.5), (12.5, 13.5), (14.5, 16.5)]
duration = 30  # 30 minutes

print(schedule_meeting(jack_schedule, charlotte_schedule, duration, {}))