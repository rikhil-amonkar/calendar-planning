from z3 import *

s = Optimize()

start_time = Int('start_time')

s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # Must end by 17:00 (480 minutes)
s.add(start_time >= 360)       # Angela's preference (after 15:00)

# Katherine's constraints (12:00-12:30, 13:00-14:30)
s.add(Or(start_time + 30 <= 180, start_time >= 210))
s.add(Or(start_time + 30 <= 240, start_time >= 330))

# Julie's constraints (9:00-9:30, 10:30-11:00, 13:30-14:00, 15:00-15:30)
s.add(Or(start_time + 30 <= 0, start_time >= 30))
s.add(Or(start_time + 30 <= 90, start_time >= 120))
s.add(Or(start_time + 30 <= 270, start_time >= 300))
s.add(Or(start_time + 30 <= 360, start_time >= 390))

# Angela's constraints (9:00-10:00, 10:30-11:00, 11:30-14:00, 14:30-15:00, 16:30-17:00)
s.add(Or(start_time + 30 <= 0, start_time >= 60))
s.add(Or(start_time + 30 <= 90, start_time >= 120))
s.add(Or(start_time + 30 <= 150, start_time >= 300))
s.add(Or(start_time + 30 <= 330, start_time >= 360))
s.add(Or(start_time + 30 <= 450, start_time >= 480))

# Nicholas's constraints (9:30-11:00, 11:30-13:30, 14:00-16:00, 16:30-17:00)
s.add(Or(start_time + 30 <= 30, start_time >= 120))
s.add(Or(start_time + 30 <= 150, start_time >= 240))
s.add(Or(start_time + 30 <= 300, start_time >= 420))
s.add(Or(start_time + 30 <= 450, start_time >= 480))

# Carl's constraints (9:00-11:00, 11:30-12:30, 13:00-14:30, 15:00-16:00, 16:30-17:00)
s.add(Or(start_time + 30 <= 0, start_time >= 120))
s.add(Or(start_time + 30 <= 150, start_time >= 180))
s.add(Or(start_time + 30 <= 240, start_time >= 330))
s.add(Or(start_time + 30 <= 360, start_time >= 420))
s.add(Or(start_time + 30 <= 450, start_time >= 480))

s.minimize(start_time)

if s.check() == sat:
    m = s.model()
    st = m[start_time].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")