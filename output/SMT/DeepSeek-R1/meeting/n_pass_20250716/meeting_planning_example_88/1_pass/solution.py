from z3 import *

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Time in minutes from midnight
start_time = 9 * 60       # 9:00 AM
joshua_start = 20 * 60 + 45  # 8:45 PM
joshua_end = 21 * 60 + 45    # 9:45 PM

# Create an optimizer
opt = Optimize()

# Define variables
T_leave_SD = Int('T_leave_SD')        # Time leaving Sunset District
T_arrive_GGP = T_leave_SD + 11        # Time arriving at Golden Gate Park
T_leave_GGP = Int('T_leave_GGP')      # Time leaving Golden Gate Park

# Constraints
opt.add(T_leave_SD >= start_time)     # Must leave Sunset District after 9:00 AM
opt.add(T_leave_GGP >= T_arrive_GGP)  # Leave Golden Gate Park after arrival
opt.add(T_leave_GGP <= joshua_end)    # Leave Golden Gate Park by 9:45 PM

# Meeting duration constraint
meeting_start = If(T_arrive_GGP >= joshua_start, T_arrive_GGP, joshua_start)
meeting_duration = T_leave_GGP - meeting_start
opt.add(meeting_duration >= 15)       # At least 15 minutes with Joshua

# Maximize departure time from Sunset District to leave as late as possible
opt.maximize(T_leave_SD)

if opt.check() == sat:
    m = opt.model()
    leave_SD = m.eval(T_leave_SD).as_long()
    arrive_GGP = leave_SD + 11
    leave_GGP = m.eval(T_leave_GGP).as_long()
    
    print("Leave Sunset District at:", min_to_time(leave_SD))
    print("Arrive at Golden Gate Park at:", min_to_time(arrive_GGP))
    print("Leave Golden Gate Park at:", min_to_time(leave_GGP))
else:
    print("No solution")