from z3 import *

s = Solver()
start = Int('start')
s.add(start >= 0)
s.add(start + 30 <= 480)  # Meeting must end by 17:00

# Define each participant's busy time intervals (start_minute, end_minute)
participants = [
    {  # Gregory
        'busy': [(0, 30), (150, 180)]
    },
    {  # Jonathan
        'busy': [(0, 30), (180, 210), (240, 270), (360, 420), (450, 480)]
    },
    {  # Barbara
        'busy': [(60, 90), (270, 300)]
    },
    {  # Jesse
        'busy': [(60, 120), (210, 330)]
    },
    {  # Alan
        'busy': [(30, 120), (150, 180), (240, 390), (420, 480)]
    },
    {  # Nicole
        'busy': [(0, 90), (150, 180), (210, 270), (300, 480)]
    },
    {  # Catherine
        'busy': [(0, 90), (180, 270), (360, 390), (420, 450)]
    }
]

# Add constraints for each participant's busy times
for person in participants:
    for (s_start, s_end) in person['busy']:
        s.add(Or(start + 30 <= s_start, start >= s_end))

if s.check() == sat:
    model = s.model()
    start_time = model[start].as_long()
    hours = 9 + start_time // 60
    minutes = start_time % 60
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")