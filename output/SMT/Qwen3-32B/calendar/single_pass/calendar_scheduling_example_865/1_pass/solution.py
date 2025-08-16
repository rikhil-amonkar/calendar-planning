from z3 import *

# Define the busy periods for each day and person in minutes since midnight
megan_busy = [
    # Monday (0)
    [(13*60, 13*60+30), (14*60, 15*60 + 30)],  # 13:00-13:30, 14:00-15:30
    # Tuesday (1)
    [(9*60, 9*60+30), (12*60, 12*60+30), (16*60, 17*60)],
    # Wednesday (2)
    [(9*60+30, 10*60), (10*60+30, 11*60 + 30), (12*60+30, 14*60), (16*60, 16*60+30)],
    # Thursday (3)
    [(13*60+30, 14*60 + 30), (15*60, 15*60+30)]
]

daniel_busy = [
    # Monday (0)
    [(10*60, 11*60 + 30), (12*60 + 30, 15*60)],
    # Tuesday (1)
    [(9*60, 10*60), (10*60 + 30, 17*60)],
    # Wednesday (2)
    [(9*60, 10*60), (10*60 + 30, 11*60 + 30), (12*60, 17*60)],
    # Thursday (3)
    [(9*60, 12*60), (12*60 + 30, 14*60 + 30), (15*60, 15*60+30), (16*60, 17*60)]
]

# Create variables for day and start time
day = Int('day')
start_time = Int('start_time')

opt = Optimize()

# Constraints on day and start_time
opt.add(day >= 0)
opt.add(day <= 3)
opt.add(start_time >= 9*60)  # 9:00 AM
opt.add(start_time <= 16*60) # 16:00 (meeting is 1 hour)

# For each day D, add constraints if day == D
for D in range(4):
    # Megan's constraints for day D
    m_constraints = []
    for (b_start, b_end) in meghan_busy[D]:
        # Slot [start_time, start_time + 60) does not overlap with [b_start, b_end)
        m_constraints.append(Or(start_time + 60 <= b_start, start_time >= b_end))
    # Daniel's constraints for day D
    d_constraints = []
    for (b_start, b_end) in daniel_busy[D]:
        d_constraints.append(Or(start_time + 60 <= b_start, start_time >= b_end))
    # Combine all constraints for day D
    all_constraints = And(m_constraints + d_constraints)
    # Add the implication: if day == D, then all_constraints
    opt.add(Implies(day == D, all_constraints))

# Minimize day and start_time to find the earliest possible
opt.minimize(day)
opt.minimize(start_time)

# Check if there's a solution
if opt.check() == sat:
    model = opt.model()
    d = model[day].as_long()
    st = model[start_time].as_long()
    et = st + 60
    # Convert day to name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = days[d]
    # Convert start and end times to HH:MM
    def to_time(mins):
        h = mins // 60
        m = mins % 60
        return f"{h:02d}:{m:02d}"
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {to_time(st)}")
    print(f"End Time: {to_time(et)}")
else:
    print("No solution found")