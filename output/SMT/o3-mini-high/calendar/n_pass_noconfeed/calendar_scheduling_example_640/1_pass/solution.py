from z3 import *

# Define constants
WORK_START = 9 * 60      # 9:00 in minutes from 0
WORK_END = 17 * 60       # 17:00 in minutes from 0
MEETING_DURATION = 30

# We represent the meeting start time in minutes offset from 9:00.
# Thus, valid meeting start: 0 <= meetingStart <= (WORK_END - WORK_START - MEETING_DURATION)
meetingStart_min = 0
meetingStart_max = (WORK_END - WORK_START) - MEETING_DURATION  # 480 - 30 = 450

# We'll use an integer "meetingDay" where 0 = Monday, 1 = Tuesday.
# We'll use an objective to minimize (meetingDay*10000 + meetingStart) so that any Monday meeting (day = 0)
# will be prioritized, and then the earliest time within that day.
meetingDay = Int('meetingDay')
meetingStart = Int('meetingStart')

s = Optimize()
s.add(meetingStart >= meetingStart_min, meetingStart <= meetingStart_max)
s.add(Or(meetingDay == 0, meetingDay == 1))

# To make the code more clear, we convert busy times to minutes offset from 9:00.
# Monday schedules:
# Bobby busy: 14:30 to 15:00 -> [330, 360]
# Michael busy:
#  9:00 to 10:00   -> [0, 60]
# 10:30 to 13:30   -> [90, 270]
# 14:00 to 15:00   -> [300, 360]
# 15:30 to 17:00   -> [390, 480]   (for meeting, meeting end must be <= 390)

# Tuesday schedules:
# Bobby busy:
#  9:00 to 11:30   -> [0, 150]
# 12:00 to 12:30   -> [180, 210]
# 13:00 to 15:00   -> [240, 360]
# 15:30 to 17:00   -> [390, 480]  (meeting end must be <= 390)
# Michael busy:
#  9:00 to 10:30   -> [0, 90]
# 11:00 to 11:30   -> [120, 150]
# 12:00 to 14:00   -> [180, 300]
# 15:00 to 16:00   -> [360, 420]
# 16:30 to 17:00   -> [450, 480]  (meeting end must be <= 450)

# We'll add non-overlap constraints for each busy slot valid on that day.
# The meeting [meetingStart, meetingStart+MEETING_DURATION] must either end no later than busy start
# OR start no earlier than busy end.

# Monday constraints (if meetingDay == 0)
# Bobby on Monday: busy [330, 360]
s.add(Implies(meetingDay == 0,
              Or(meetingStart + MEETING_DURATION <= 330, meetingStart >= 360)))

# Michael on Monday:
# busy [0, 60] -> meeting must start at or after 60 minutes.
s.add(Implies(meetingDay == 0, meetingStart >= 60))
# busy [90, 270]
s.add(Implies(meetingDay == 0,
              Or(meetingStart + MEETING_DURATION <= 90, meetingStart >= 270)))
# busy [300, 360]
s.add(Implies(meetingDay == 0,
              Or(meetingStart + MEETING_DURATION <= 300, meetingStart >= 360)))
# busy [390, 480] -> here, meeting start must be such that meetingStart+MEETING_DURATION <= 390
s.add(Implies(meetingDay == 0, meetingStart + MEETING_DURATION <= 390))

# Tuesday constraints (if meetingDay == 1)
# Bobby on Tuesday:
# busy [0, 150]
s.add(Implies(meetingDay == 1,
              Or(meetingStart + MEETING_DURATION <= 0, meetingStart >= 150)))
# Note: meetingStart + MEETING_DURATION <= 0 is impossible given meetingStart>=0, so effectively meetingStart >= 150.
# busy [180, 210]
s.add(Implies(meetingDay == 1,
              Or(meetingStart + MEETING_DURATION <= 180, meetingStart >= 210)))
# busy [240, 360]
s.add(Implies(meetingDay == 1,
              Or(meetingStart + MEETING_DURATION <= 240, meetingStart >= 360)))
# busy [390, 480] -> meetingStart+MEETING_DURATION <= 390
s.add(Implies(meetingDay == 1, meetingStart + MEETING_DURATION <= 390))

# Michael on Tuesday:
# busy [0, 90]
s.add(Implies(meetingDay == 1,
              Or(meetingStart + MEETING_DURATION <= 0, meetingStart >= 90)))
# busy [120, 150]
s.add(Implies(meetingDay == 1,
              Or(meetingStart + MEETING_DURATION <= 120, meetingStart >= 150)))
# busy [180, 300]
s.add(Implies(meetingDay == 1,
              Or(meetingStart + MEETING_DURATION <= 180, meetingStart >= 300)))
# busy [360, 420]
s.add(Implies(meetingDay == 1,
              Or(meetingStart + MEETING_DURATION <= 360, meetingStart >= 420)))
# busy [450, 480] -> meetingStart+MEETING_DURATION <= 450
s.add(Implies(meetingDay == 1, meetingStart + MEETING_DURATION <= 450))

# Add objective: earliest available meeting.
# We want to schedule as early as possible overall. Note that Monday (day==0) should be prioritized.
# We create a combined objective: day*big_constant + meetingStart, where big_constant > max(meetingStart)
big_constant = 10000
objective = meetingDay * big_constant + meetingStart
s.minimize(objective)

if s.check() == sat:
    m = s.model()
    day_val = m.evaluate(meetingDay).as_long()
    start_val = m.evaluate(meetingStart).as_long()
    end_val = start_val + MEETING_DURATION

    # Convert minutes offset from 9:00 to actual HH:MM.
    def convert(minutes_offset):
        total_minutes = WORK_START + minutes_offset
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return hours, minutes

    start_hour, start_min = convert(start_val)
    end_hour, end_min = convert(end_val)
    day_str = "Monday" if day_val == 0 else "Tuesday"

    # Format the meeting time as HH:MM:HH:MM
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print(f"Proposed meeting time: {time_str} on {day_str}")
else:
    print("No solution found.")