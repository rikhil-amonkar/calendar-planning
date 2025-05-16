from z3 import Solver, Int, Or, sat

solver = Solver()
S = Int('S')

# Meeting must be within 9:00 to 17:00 (480 minutes) and after 14:00 (Wayne's preference)
solver.add(S >= 300)  # 14:00 = 300 minutes after 9:00
solver.add(S + 30 <= 480)

# Melissa's blocked times (10:00-11:00=60-120, 12:30-14:00=150-240, 15:00-15:30=360-390)
melissa_blocks = [(60, 120), (150, 240), (360, 390)]
for start, end in melissa_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Gregory's blocked times (12:30-13:00=210-240, 15:30-16:00=330-360)
gregory_blocks = [(210, 240), (330, 360)]
for start, end in gregory_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Victoria's blocked times (9:00-9:30=0-30, 10:30-11:30=90-150, 13:00-14:00=240-300, 14:30-15:00=330-360, 15:30-16:30=390-420)
victoria_blocks = [(0, 30), (90, 150), (240, 300), (330, 360), (390, 420)]
for start, end in victoria_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Thomas's blocked times (10:00-12:00=60-180, 12:30-13:00=210-240, 14:30-16:00=330-420)
thomas_blocks = [(60, 180), (210, 240), (330, 420)]
for start, end in thomas_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Jennifer's blocked times (9:00-9:30=0-30, 10:00-10:30=60-90, 11:00-13:00=120-240, 13:30-14:30=270-330, 15:00-15:30=360-390, 16:00-16:30=420-450)
jennifer_blocks = [(0, 30), (60, 90), (120, 240), (270, 330), (360, 390), (420, 450)]
for start, end in jennifer_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Wayne and Catherine have no constraints beyond Wayne's initial time preference

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