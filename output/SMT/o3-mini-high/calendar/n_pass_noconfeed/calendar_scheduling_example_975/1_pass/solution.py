from z3 import *

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    work_start = 9 * 60      # 9:00 in minutes (540)
    work_end   = 17 * 60     # 17:00 in minutes (1020)
    meeting_duration = 60

    # Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday.
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

    # Create an Optimize object
    opt = Optimize()

    # Define the two decision variables:
    day = Int("day")    # Day index: 0-4
    start = Int("start")  # Meeting start time in minutes since midnight
    end = start + meeting_duration

    # Domain constraints:
    opt.add(And(day >= 0, day <= 4))
    # The meeting must start no earlier than 9:00 and finish by 17:00.
    opt.add(And(start >= work_start, end <= work_end))

    # Helper: for any busy interval [b_start, b_end], the meeting [start, end)
    # must satisfy either end <= b_start or start >= b_end.

    # -------------------------
    # Nicole's Busy Intervals
    # Tuesday: 16:00 - 16:30  -> [960, 990]
    opt.add(Implies(day == 1, Or(end <= 960, start >= 990)))
    # Wednesday: 15:00 - 15:30 -> [900, 930]
    opt.add(Implies(day == 2, Or(end <= 900, start >= 930)))
    # Friday: two intervals
    #   12:00 - 12:30 -> [720, 750]
    opt.add(Implies(day == 4, Or(end <= 720, start >= 750)))
    #   15:30 - 16:00 -> [930, 960]
    opt.add(Implies(day == 4, Or(end <= 930, start >= 960)))
    
    # -------------------------
    # Daniel's Busy Intervals
    # Monday (day==0):
    #   9:00 - 12:30 -> [540, 750]
    opt.add(Implies(day == 0, Or(end <= 540, start >= 750)))
    #   13:00 - 13:30 -> [780, 810]
    opt.add(Implies(day == 0, Or(end <= 780, start >= 810)))
    #   14:00 - 16:30 -> [840, 990]
    opt.add(Implies(day == 0, Or(end <= 840, start >= 990)))
    
    # Tuesday (day==1):
    #   9:00 - 10:30 -> [540, 630]
    opt.add(Implies(day == 1, Or(end <= 540, start >= 630)))
    #   11:30 - 12:30 -> [690, 750]
    opt.add(Implies(day == 1, Or(end <= 690, start >= 750)))
    #   13:00 - 13:30 -> [780, 810]
    opt.add(Implies(day == 1, Or(end <= 780, start >= 810)))
    #   15:00 - 16:00 -> [900, 960]
    opt.add(Implies(day == 1, Or(end <= 900, start >= 960)))
    #   16:30 - 17:00 -> [990, 1020]
    opt.add(Implies(day == 1, Or(end <= 990, start >= 1020)))
    
    # Wednesday (day==2):
    #   9:00 - 10:00 -> [540, 600]
    opt.add(Implies(day == 2, Or(end <= 540, start >= 600)))
    #   11:00 - 12:30 -> [660, 750]
    opt.add(Implies(day == 2, Or(end <= 660, start >= 750)))
    #   13:00 - 13:30 -> [780, 810]
    opt.add(Implies(day == 2, Or(end <= 780, start >= 810)))
    #   14:00 - 14:30 -> [840, 870]
    opt.add(Implies(day == 2, Or(end <= 840, start >= 870)))
    #   16:30 - 17:00 -> [990, 1020]
    opt.add(Implies(day == 2, Or(end <= 990, start >= 1020)))
    
    # Thursday (day==3):
    #   11:00 - 12:00 -> [660, 720]
    opt.add(Implies(day == 3, Or(end <= 660, start >= 720)))
    #   13:00 - 14:00 -> [780, 840]
    opt.add(Implies(day == 3, Or(end <= 780, start >= 840)))
    #   15:00 - 15:30 -> [900, 930]
    opt.add(Implies(day == 3, Or(end <= 900, start >= 930)))
    
    # Friday (day==4):
    # Daniel's schedule on Friday:
    #   10:00 - 11:00 -> [600, 660]
    opt.add(Implies(day == 4, Or(end <= 600, start >= 660)))
    #   11:30 - 12:00 -> [690, 720]
    opt.add(Implies(day == 4, Or(end <= 690, start >= 720)))
    #   12:30 - 14:30 -> [750, 870]
    opt.add(Implies(day == 4, Or(end <= 750, start >= 870)))
    #   15:00 - 15:30 -> [900, 930]
    opt.add(Implies(day == 4, Or(end <= 900, start >= 930)))
    #   16:00 - 16:30 -> [960, 990]
    opt.add(Implies(day == 4, Or(end <= 960, start >= 990)))

    # -------------------------
    # Objective: the group wants the earliest available time.
    # We define a composite objective: day*10000 + start ensures that the day is prioritized, and then the time.
    opt.minimize(day * 10000 + start)

    # Check for satisfiability and obtain the solution
    if opt.check() == sat:
        model = opt.model()
        selected_day = model[day].as_long()
        selected_start = model[start].as_long()
        selected_end = selected_start + meeting_duration
        print(day_names[selected_day])
        print(f"{minutes_to_time(selected_start)}:{minutes_to_time(selected_end)}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()