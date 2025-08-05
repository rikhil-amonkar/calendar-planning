import z3

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Busy intervals in minutes
lisa_busy = [
    ("9:00", "10:00"),
    ("10:30", "11:30"),
    ("12:30", "13:00"),
    ("16:00", "16:30")
]
lisa_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in lisa_busy]

bobby_busy = [
    ("9:00", "9:30"),
    ("10:00", "10:30"),
    ("11:30", "12:00"),
    ("15:00", "15:30")
]
bobby_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in bobby_busy]

randy_busy = [
    ("9:30", "10:00"),
    ("10:30", "11:00"),
    ("11:30", "12:30"),
    ("13:00", "13:30"),
    ("14:30", "15:30"),
    ("16:00", "16:30")
]
randy_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in randy_busy]

s = z3.Solver()
start = z3.Int('start')
end = start + 30  # meeting duration

# Work hours: 9:00 (540) to 17:00 (1020)
s.add(start >= 540)
s.add(end <= 1020)

# Function to add no-overlap constraints
def add_no_overlap_constraints(intervals):
    for (busy_start, busy_end) in intervals:
        s.add(z3.Or(end <= busy_start, start >= busy_end))

add_no_overlap_constraints(lisa_intervals)
add_no_overlap_constraints(bobby_intervals)
add_no_overlap_constraints(randy_intervals)

# First, try to respect Bobby's preference: meeting ends by 15:00 (900 minutes)
s.push()
s.add(end <= 900)

if s.check() == z3.sat:
    m = s.model()
    start_min = m[start].as_long()
    end_min = start_min + 30
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(end_min)
    solution_found = True
else:
    s.pop()  # Remove the preference constraint
    if s.check() == z3.sat:
        m = s.model()
        start_min = m[start].as_long()
        end_min = start_min + 30
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        solution_found = True
    else:
        solution_found = False

if solution_found:
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")