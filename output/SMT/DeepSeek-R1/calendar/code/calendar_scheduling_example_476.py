from z3 import Solver, Int, Or, sat

solver = Solver()
S = Int('S')

# Meeting must be within 9:00 to 17:00 (480 minutes) and start after 12:30 (Roger's preference)
solver.add(S >= 210)  # 12:30 = 210 minutes after 9:00
solver.add(S + 30 <= 480)

# Kathleen's blocked times (14:30-15:30 = 330-390 minutes)
kathleen_blocks = [(330, 390)]
for start, end in kathleen_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Carolyn's blocked times (12:00-12:30=180-210, 13:00-13:30=240-270)
carolyn_blocks = [(180, 210), (240, 270)]
for start, end in carolyn_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Cheryl's blocked times (9:00-9:30=0-30, 10:00-11:30=60-150, 12:30-13:30=210-270, 14:00-17:00=300-480)
cheryl_blocks = [(0, 30), (60, 150), (210, 270), (300, 480)]
for start, end in cheryl_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Virginia's blocked times (9:30-11:30=30-150, 12:00-12:30=180-210, 13:00-13:30=240-270, 14:30-15:30=330-390, 16:00-17:00=420-480)
virginia_blocks = [(30, 150), (180, 210), (240, 270), (330, 390), (420, 480)]
for start, end in virginia_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Angela's blocked times (9:30-10:00=30-60, 10:30-11:30=90-150, 12:00-12:30=180-210, 13:00-13:30=240-270, 14:00-16:30=300-450)
angela_blocks = [(30, 60), (90, 150), (180, 210), (240, 270), (300, 450)]
for start, end in angela_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Daniel and Roger have no constraints beyond Roger's initial time preference

if solver.check() == sat:
    model = solver.model()
    start_min = model[S].as_long()
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 30
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")