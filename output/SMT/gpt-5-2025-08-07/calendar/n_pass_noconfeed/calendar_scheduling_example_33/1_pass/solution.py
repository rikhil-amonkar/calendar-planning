from z3 import *

def hm_to_min(hm):
    h, m = map(int, hm.split(":"))
    return h*60 + m

def min_to_hm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Meeting parameters
day = "Monday"
work_start = hm_to_min("09:00")
work_end   = hm_to_min("17:00")
duration = 30  # minutes

# Busy schedules (inclusive of start, exclusive of end)
lisa_busy = [
    ("09:00","10:00"),
    ("10:30","11:30"),
    ("12:30","13:00"),
    ("16:00","16:30"),
]
bobby_busy = [
    ("09:00","09:30"),
    ("10:00","10:30"),
    ("11:30","12:00"),
    ("15:00","15:30"),
]
randy_busy = [
    ("09:30","10:00"),
    ("10:30","11:00"),
    ("11:30","12:30"),
    ("13:00","13:30"),
    ("14:30","15:30"),
    ("16:00","16:30"),
]

# Convert to minute intervals
def convert_blocks(blocks):
    return [(hm_to_min(s), hm_to_min(e)) for s, e in blocks]

lisa_busy = convert_blocks(lisa_busy)
bobby_busy = convert_blocks(bobby_busy)
randy_busy = convert_blocks(randy_busy)

# Z3 model
opt = Optimize()
s = Int('start')

# Meeting within work hours
opt.add(s >= work_start, s + duration <= work_end)

# Start time aligned to 30-minute grid
opt.add(s % 30 == 0)

# Non-overlap with each participant's busy times
def add_non_overlap(busy_list):
    for a, b in busy_list:
        # meeting [s, s+duration) must not overlap [a, b)
        opt.add(Or(s + duration <= a, s >= b))

add_non_overlap(lisa_busy)
add_non_overlap(bobby_busy)
add_non_overlap(randy_busy)

# Preference: Bobby would like to avoid meetings after 15:00
# Soft constraint: prefer the meeting to end by 15:00
pref_deadline = hm_to_min("15:00")
opt.add_soft(s + duration <= pref_deadline, weight=1)

# Tie-breaker: choose the earliest start that satisfies preferences
opt.minimize(s)

if opt.check() == sat:
    m = opt.model()
    start_min = m[s].as_long()
    end_min = start_min + duration
    start_str = min_to_hm(start_min)
    end_str = min_to_hm(end_min)
    # Output format: Day {HH:MM:HH:MM}
    print(f"{day} {{{start_str}:{end_str}}}")
else:
    print("No feasible time found.")