from z3 import *

# Represent time in minutes from midnight.
# 9:00 AM is 540 and 17:00 is 1020.
meeting_start = Int('meeting_start')
meeting_duration = 60

s = Solver()

# Meeting must start no earlier than 9:00 and end by 17:00.
s.add(meeting_start >= 540)
s.add(meeting_start + meeting_duration <= 1020)

# Kayla's busy intervals:
# Interval 1: 10:00-10:30 -> [600, 630]
# Interval 2: 14:30-16:00 -> [870, 960]
# For each busy interval, the meeting must either finish before it starts or start after it ends.
s.add(Or(meeting_start + meeting_duration <= 600, meeting_start >= 630))
s.add(Or(meeting_start + meeting_duration <= 870, meeting_start >= 960))

# Rebecca's busy intervals:
# Interval 1: 9:00-13:00 -> [540, 780]
# Interval 2: 13:30-15:00 -> [810, 900]
# Interval 3: 15:30-16:00 -> [930, 960]
s.add(Or(meeting_start + meeting_duration <= 540, meeting_start >= 780))
s.add(Or(meeting_start + meeting_duration <= 810, meeting_start >= 900))
s.add(Or(meeting_start + meeting_duration <= 930, meeting_start >= 960))

if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    
    # Convert minutes to HH:MM format.
    def minutes_to_hhmm(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", minutes_to_hhmm(start_time))
    print("End Time:", minutes_to_hhmm(end_time))
else:
    print("No solution found.")