from z3 import Solver, Int, Or, If, sat

s = Solver()
day = Int('day')
start = Int('start')

# Define day and start constraints
s.add(day >= 0, day <= 4)  # 0=Monday, 4=Friday
s.add(start >= 0, start + 60 <= 480)  # Total work hours 9:00-17:00 (480 minutes)

# Nicole's busy intervals (day, start_min, end_min)
nicole_busy = [
    (1, 420, 450),   # Tuesday 16:00-16:30
    (2, 360, 390),   # Wednesday 15:00-15:30
    (4, 180, 210),   # Friday 12:00-12:30
    (4, 390, 420)    # Friday 15:30-16:00
]

# Daniel's busy intervals (day, start_min, end_min)
daniel_busy = [
    (0, 0, 210), (0, 240, 270), (0, 300, 450),          # Monday
    (1, 0, 90), (1, 150, 180), (1, 240, 270),            # Tuesday
    (1, 360, 420), (1, 450, 480),                        # Tuesday
    (2, 0, 60), (2, 120, 210), (2, 240, 270),            # Wednesday
    (2, 300, 330), (2, 450, 480),                        # Wednesday
    (3, 120, 180), (3, 240, 300), (3, 360, 390),         # Thursday
    (4, 60, 120), (4, 150, 180), (4, 210, 330),          # Friday
    (4, 360, 390), (4, 420, 450)                         # Friday
]

# Add Nicole's constraints
for d, s_start, s_end in nicole_busy:
    s.add(If(day == d, Or(start + 60 <= s_start, start >= s_end), True))

# Add Daniel's constraints
for d, s_start, s_end in daniel_busy:
    s.add(If(day == d, Or(start + 60 <= s_start, start >= s_end), True))

# Optimize for earliest day and earliest time
s.minimize(day * 1000 + start)  # Prioritize day first, then start time

if s.check() == sat:
    m = s.model()
    best_day = m[day].as_long()
    start_time = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    hours = start_time // 60 + 9
    minutes = start_time % 60
    print(f"Meeting starts on {days[best_day]} at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")