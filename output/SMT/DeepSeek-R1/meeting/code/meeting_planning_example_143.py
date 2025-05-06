from z3 import *

s = Solver()

# Define start times (Karen's start is fixed at 6:45 PM = 1125 minutes)
Mark_start = Int('Mark_start')
Karen_start = 1125  # 18:45 in minutes

# Mark's availability constraints (1:00 PM to 5:45 PM)
s.add(Mark_start >= 780)          # Earliest start 1:00 PM (780)
s.add(Mark_start + 120 <= 1065)   # Must end by 5:45 PM (1065)

# Travel constraints from North Beach to Embarcadero (first meeting)
s.add(Mark_start - 6 >= 540)      # Departure after 9:00 AM arrival

# Travel from Mark's location to Karen's location
travel_time = 11  # Embarcadero to Pacific Heights
s.add(Mark_start + 120 + travel_time <= Karen_start)  # Arrive before Karen's meeting

if s.check() == sat:
    m = s.model()
    ms = m[Mark_start].as_long()
    me = ms + 120
    print("Optimal Schedule:")
    print(f"Mark: {ms//60:02d}:{ms%60:02d} - {me//60:02d}:{me%60:02d}")
    print(f"Karen: 18:45 - 20:15")  # Fixed meeting time
else:
    print("No valid schedule found (can only meet one friend).")