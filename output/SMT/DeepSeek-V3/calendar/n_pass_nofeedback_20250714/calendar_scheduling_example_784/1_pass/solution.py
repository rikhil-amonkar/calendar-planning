from z3 import *

def solve_scheduling_problem():
    # Create the solver
    s = Solver()

    # Define the possible days
    days = ['Monday', 'Tuesday', 'Wednesday']
    day = Int('day')
    s.add(day >= 0, day < len(days))  # 0: Monday, 1: Tuesday, 2: Wednesday

    # Define the start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 60)  # 17:00 is 1020 minutes, meeting is 60 minutes

    # Meeting duration is fixed to 1 hour (60 minutes)
    end_time = start_time + 60

    # Define the constraints based on Judith and Timothy's schedules
    # Judith's blocked times:
    judith_blocked = [
        ('Monday', 12*60, 12*60 + 30),    # Monday 12:00-12:30
        ('Wednesday', 11*60 + 30, 12*60)  # Wednesday 11:30-12:00
    ]
    # Timothy's blocked times:
    timothy_blocked = [
        ('Monday', 9*60 + 30, 10*60),      # Monday 9:30-10:00
        ('Monday', 10*60 + 30, 11*60 + 30), # Monday 10:30-11:30
        ('Monday', 12*60 + 30, 14*60),     # Monday 12:30-14:00
        ('Monday', 15*60 + 30, 17*60),     # Monday 15:30-17:00
        ('Tuesday', 9*60 + 30, 13*60),     # Tuesday 9:30-13:00
        ('Tuesday', 13*60 + 30, 14*60),    # Tuesday 13:30-14:00
        ('Tuesday', 14*60 + 30, 17*60),    # Tuesday 14:30-17:00
        ('Wednesday', 9*60, 9*60 + 30),    # Wednesday 9:00-9:30
        ('Wednesday', 10*60 + 30, 11*60),  # Wednesday 10:30-11:00
        ('Wednesday', 13*60 + 30, 14*60 + 30), # Wednesday 13:30-14:30
        ('Wednesday', 15*60, 15*60 + 30),  # Wednesday 15:00-15:30
        ('Wednesday', 16*60, 16*60 + 30)   # Wednesday 16:00-16:30
    ]

    # Function to check if two intervals overlap
    def overlaps(a_start, a_end, b_start, b_end):
        return Not(Or(a_end <= b_start, b_end <= a_start))

    # Add constraints for Judith's blocked times
    for blocked_day, block_start, block_end in judith_blocked:
        day_idx = days.index(blocked_day)
        s.add(Not(And(day == day_idx, overlaps(start_time, end_time, block_start, block_end))))

    # Add constraints for Timothy's blocked times
    for blocked_day, block_start, block_end in timothy_blocked:
        day_idx = days.index(blocked_day)
        s.add(Not(And(day == day_idx, overlaps(start_time, end_time, block_start, block_end))))

    # Add Judith's preferences: avoid more meetings on Monday and before 12:00 on Wednesday
    s.add(Not(And(day == 0)))  # Avoid Monday
    s.add(Not(And(day == 2, start_time < 12*60)))  # Avoid Wednesday before 12:00

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        day_idx = model[day].as_long()
        start_min = model[start_time].as_long()
        end_min = start_min + 60

        # Convert minutes back to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_hh = end_min // 60
        end_mm = end_min % 60

        # Format the output
        solution = f"SOLUTION:\nDay: {days[day_idx]}\nStart Time: {start_hh:02d}:{start_mm:02d}\nEnd Time: {end_hh:02d}:{end_mm:02d}"
        print(solution)
    else:
        print("No solution found")

solve_scheduling_problem()