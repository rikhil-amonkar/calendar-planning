from z3 import *

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

# Convert the schedules into minutes from 9:00
megan_busy = {
    0: [  # Monday
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ]
}

daniel_busy = {
    0: [  # Monday
        (time_to_minutes("10:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("15:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("09:00"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
}

# Create Z3 variables
day = Int('day')
start_time = Int('start_time')

# Create a solver instance
s = Solver()

# Day must be 0, 1, 2, or 3 (Monday to Thursday)
s.add(day >= 0, day <= 3)

# Start time must be between 0 and 420 minutes (so that the meeting ends by 17:00)
s.add(start_time >= 0, start_time <= 420)

# For each day, add constraints that the meeting does not overlap with any busy interval
for d in range(4):
    megan_constraints = []
    for busy_start, busy_end in megan_busy.get(d, []):
        megan_constraints.append(Or(start_time >= busy_end, start_time + 60 <= busy_start))
    daniel_constraints = []
    for busy_start, busy_end in daniel_busy.get(d, []):
        daniel_constraints.append(Or(start_time >= busy_end, start_time + 60 <= busy_start))
    
    # Combine constraints for the day
    day_constraint = And(And(megan_constraints), And(daniel_constraints))
    # If the meeting is on day `d`, then the constraints must hold
    s.add(Implies(day == d, day_constraint))

# We want the earliest time: minimize (day * 480 + start_time)
objective = day * 480 + start_time
opt = Optimize()
opt.minimize(objective)
opt.add(s.assertions())

# Check for a solution
if opt.check() == sat:
    m = opt.model()
    day_val = m[day].as_long()
    start_val = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[day_val]
    
    # Convert start minutes to time string
    total_minutes = start_val
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    start_str = f"{hour:02d}:{minute:02d}"
    
    # Calculate end time
    end_minutes = start_val + 60
    end_hour = 9 + end_minutes // 60
    end_minute = end_minutes % 60
    end_str = f"{end_hour:02d}:{end_minute:02d}"
    
    print(f"Day: {day_name}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found")