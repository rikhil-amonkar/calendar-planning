from z3 import *

def main():
    # Meeting parameters
    meeting_duration = 30  # in minutes
    work_start = 9 * 60    # 9:00 as minutes (540)
    work_end = 17 * 60     # 17:00 as minutes (1020)
    
    # Create Z3 solver instance
    solver = Solver()

    # Define variables:
    # day: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
    day = Int('day')
    # start: meeting start time in minutes (from midnight)
    start = Int('start')
    end = start + meeting_duration  # meeting end time

    # Allowed days: Monday, Tuesday or Wednesday.
    solver.add(Or(day == 0, day == 1, day == 2))
    
    # Meeting must be within working hours.
    solver.add(start >= work_start)
    solver.add(end <= work_end)
    
    # -----------------------
    # Busy intervals constraints
    # For each busy interval on a given day, if the meeting is scheduled on that day
    # then the meeting must either end before the busy period starts or start after it ends.
    
    # Tyler's busy intervals:
    # Tuesday (day == 1):
    #   9:00 to 9:30 -> [540, 570]
    solver.add(Implies(day == 1, Or(end <= 540, start >= 570)))
    #   14:30 to 15:00 -> [870, 900]
    solver.add(Implies(day == 1, Or(end <= 870, start >= 900)))
    
    # Wednesday (day == 2):
    #   10:30 to 11:00 -> [630, 660]
    solver.add(Implies(day == 2, Or(end <= 630, start >= 660)))
    #   12:30 to 13:00 -> [750, 780]
    solver.add(Implies(day == 2, Or(end <= 750, start >= 780)))
    #   13:30 to 14:00 -> [810, 840]
    solver.add(Implies(day == 2, Or(end <= 810, start >= 840)))
    #   16:30 to 17:00 -> [990, 1020]
    solver.add(Implies(day == 2, Or(end <= 990, start >= 1020)))
    
    # Ruth's busy intervals:
    # Monday (day == 0):
    #   9:00 to 10:00 -> [540, 600]
    solver.add(Implies(day == 0, Or(end <= 540, start >= 600)))
    #   10:30 to 12:00 -> [630, 720]
    solver.add(Implies(day == 0, Or(end <= 630, start >= 720)))
    #   12:30 to 14:30 -> [750, 870]
    solver.add(Implies(day == 0, Or(end <= 750, start >= 870)))
    #   15:00 to 16:00 -> [900, 960]
    solver.add(Implies(day == 0, Or(end <= 900, start >= 960)))
    #   16:30 to 17:00 -> [990, 1020]
    solver.add(Implies(day == 0, Or(end <= 990, start >= 1020)))
    
    # Tuesday (day == 1): whole day busy [540, 1020]
    solver.add(Implies(day == 1, Or(end <= 540, start >= 1020)))
    
    # Wednesday (day == 2): whole day busy [540, 1020]
    solver.add(Implies(day == 2, Or(end <= 540, start >= 1020)))
    
    # -----------------------
    # Additional constraint:
    # Tyler prefers to avoid meetings on Monday before 16:00 (i.e. before 960 minutes).
    solver.add(Implies(day == 0, start >= 16 * 60))
    
    # Check for satisfiability and, if successful, extract a solution.
    if solver.check() == sat:
        model = solver.model()
        sol_day = model[day].as_long()
        sol_start = model[start].as_long()
        sol_end = model[end].as_long()

        # Helper function to convert minutes to HH:MM string.
        def format_time(t):
            hour = t // 60
            minute = t % 60
            return f"{hour:02d}:{minute:02d}"
        
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        day_str = day_names.get(sol_day, "Unknown")
        time_range = f"{format_time(sol_start)}:{format_time(sol_end)}"
        print(f"{day_str} {time_range}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()