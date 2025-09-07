from z3 import Optimize, Int, Implies

# Define meeting duration in minutes.
MEETING_DURATION = 30

# Define minutes from midnight for work hours.
WORK_START = 9 * 60   # 09:00 => 540
WORK_END = 17 * 60    # 17:00 => 1020
LATEST_START = WORK_END - MEETING_DURATION  # Latest possible start

# Define day codes: 0 for Monday, 1 for Tuesday.
monday, tuesday = 0, 1

# Create optimizer instance so we can add soft preferences.
opt = Optimize()

# Define variables: meeting start time (in minutes) and day.
start = Int('start')  # Start time in minutes from midnight.
day = Int('day')      # 0: Monday, 1: Tuesday

# The meeting must be within work hours.
opt.add(start >= WORK_START, start <= LATEST_START)

# The meeting must be scheduled on either Monday or Tuesday.
opt.add(day == monday or day == tuesday)

# Jeffrey is free the entire week, so no constraints from his side.

# Harold's blocked times and his preferences:

# For Monday:
#   Harold is busy from 9:00-10:00 and 10:30-17:00.
#   Thus, the only possible Monday slot is exactly 10:00 to 10:30.
opt.add(Implies(day == monday, start >= 10 * 60 and start + MEETING_DURATION <= 10 * 60 + 30))

# For Tuesday:
#   Harold is busy during:
#     9:00-9:30, 10:30-11:30, 12:30-13:30, 14:30-15:30, and 16:00-17:00.
#   So his free intervals are: [9:30,10:30], [11:30,12:30], [13:30,14:30], and [15:30,16:00].
#   But he would like to avoid any meeting on Tuesday that starts before 14:30.
#   This leaves only a single valid option: 15:30 to 16:00.
opt.add(Implies(day == tuesday, start >= 15 * 60 + 30 and start + MEETING_DURATION <= 16 * 60))

# Preference: Harold would like to avoid more meetings on Monday.
# We add a soft constraint to prefer Tuesday.
opt.add_soft(day == tuesday)

# Check for a solution.
if opt.check() == "sat":
    model = opt.model()
    chosen_day = model[day].as_long()
    chosen_start = model[start].as_long()
    meeting_end = chosen_start + MEETING_DURATION

    # Convert minutes into HH:MM format.
    def minutes_to_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = minutes_to_str(chosen_start)
    end_str = minutes_to_str(meeting_end)

    day_str = "Monday" if chosen_day == monday else "Tuesday"

    # Output in the required format: HH:MM:HH:MM and the day of the week.
    print(f"{start_str}:{end_str} {day_str}")
else:
    print("No valid meeting time found.")