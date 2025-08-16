from z3 import Optimize, Int, And, Or, Implies

# We'll use an integer for the day:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday.
# Because Brian wants to avoid Monday, we add the constraint day != 0.

# We'll represent time in minutes from midnight.
# The work day is 9:00 (540 minutes) to 17:00 (1020 minutes).
# Since the meeting lasts 60 minutes, the start must be between 540 and 960 minutes.

# Create variables
day = Int('day')
start = Int('start')

# Map days to their names for printing later
day_names = {0:"Monday", 1:"Tuesday", 2:"Wednesday", 3:"Thursday", 4:"Friday"}

# Collect constraints in a list
constraints = []

# Domain constraints
constraints.append(And(start >= 540, start <= 960))
constraints.append(And(day >= 0, day <= 4))
# Respect Brian’s preference to avoid Monday:
constraints.append(day != 0)

# For each day, we have to ensure the meeting (from start to start+60) does not conflict with any busy times.
# We pre-calculate the free “slots” (as allowed intervals for the meeting start time) based on each participant’s schedule.
#
# For convenience we convert times to minutes from midnight:
#  9:00 -> 540, 9:30 -> 570, 10:00 -> 600, 10:30 -> 630, 11:00 -> 660, 11:30 -> 690,
# 12:30 -> 750, 13:00 -> 780, 13:30 -> 810, 14:00 -> 840, 14:30 -> 870,
# 15:00 -> 900, 15:30 -> 930, 16:00 -> 960, 16:30 -> 990, 17:00 -> 1020.
#
# --- Monday (day==0) ---
# Brian is busy Monday: [9:30,10:00] (570-600), [12:30,14:30] (750-870), [15:30,16:00] (930-960).
# => Brian’s free intervals Monday:
#    [9:00, 9:30] (540-570),
#    [10:00, 12:30] (600-750),
#    [14:30, 15:30] (870-930),
#    [16:00, 17:00] (960-1020).
#
# Julia is busy Monday: [9:00,10:00] (540-600), [11:00,11:30] (660-690), [12:30,13:00] (750-780), [15:30,16:00] (930-960).
# => Julia’s free intervals Monday:
#    [10:00,11:00] (600-660),
#    [11:30,12:30] (690-750),
#    [13:00,15:30] (780-930),
#    [16:00,17:00] (960-1020).
#
# Their intersection gives these candidate meeting slots (meeting must last 60 minutes, so the start time is fixed in these windows):
#   • Intersection of Brian’s [10:00,12:30] and Julia’s [10:00,11:00] is [10:00,11:00].
#     (Only possibility: start exactly at 10:00.)
#   • Intersection of Brian’s [14:30,15:30] and Julia’s [13:00,15:30] is [14:30,15:30].
#     (Only possibility: start exactly at 14:30.)
#   • Intersection of Brian’s [16:00,17:00] and Julia’s [16:00,17:00] is [16:00,17:00].
#     (Only possibility: start exactly at 16:00.)
# (Although Monday has available slots, Brian prefers to avoid Monday.)

# --- Tuesday (day==1) ---
# Brian busy Tuesday: [9:00,9:30] (540-570); free: [9:30,17:00] (570-1020).
# Julia busy Tuesday: [13:00,14:00] (780-840) and [16:00,16:30] (960-990);
# Julia’s free Tuesday:
#    [9:00,13:00] (540-780) and [14:00,16:00] (840-960) and [16:30,17:00] (990-1020, too short for an hour).
#
# Intersection for Tuesday:
#   • Intersection between Brian’s [9:30,17:00] (570-1020) and Julia’s [9:00,13:00] (540-780) is [9:30,13:00] (570-780).
#     The meeting must finish by 13:00 so start must be ≤ 780-60 = 720.
#     Valid start times here are any in the interval [570,720].
#   • Also [14:00,16:00] (840-960) is valid if meeting starts in [840,960-60]=[840,900],
#     but the earliest possibility is in the first interval.
#
# We’ll allow the meeting to start anywhere in [570,720] if day==1.

interval_tuesday = Or(And(start >= 570, start <= 720),
                      And(start >= 840, start <= 900))

# --- Wednesday (day==2) ---
# Brian busy Wednesday: [12:30,14:00] (750-840), [16:30,17:00] (990-1020).
# Brian’s free Wednesday:
#    [9:00,12:30] (540-750) and [14:00,16:30] (840-990).
#
# Julia busy Wednesday: [9:00,11:30] (540-690), [12:00,12:30] (720-750), [13:00,17:00] (780-1020).
# Julia’s free Wednesday:
#   Only a tiny interval [11:30,12:00] (690-720) is free before her 13:00 block,
#   which is too short for a 60‐minute meeting.
#
# So no valid one‐hour slot exists on Wednesday.
interval_wednesday = False

# --- Thursday (day==3) ---
# Brian busy Thursday: [11:00,11:30] (660-690), [13:00,13:30] (780-810), [16:30,17:00] (990-1020).
# Brian’s free Thursday:
#   [9:00,11:00] (540-660), [11:30,13:00] (690-780), [13:30,16:30] (810-990).
#
# Julia busy Thursday: [9:00,10:30] (540-630) and [11:00,17:00] (660-1020).
# Julia’s free Thursday:
#   Only the gap between 10:30 and 11:00 (630-660) is free, which lasts just 30 minutes.
#
# So no one‐hour meeting fits on Thursday.
interval_thursday = False

# --- Friday (day==4) ---
# Brian busy Friday: [9:30,10:00] (570-600), [10:30,11:00] (630-660), [13:00,13:30] (780-810),
#                     [15:00,16:00] (900-960), [16:30,17:00] (990-1020).
# Brian’s free Friday:
#   [9:00,9:30] (540-570), [10:00,10:30] (600-630), [11:00,13:00] (660-780),
#   [13:30,15:00] (810-900), [16:00,16:30] (960-990).
#
# Julia busy Friday: [9:00,10:00] (540-600), [10:30,11:30] (630-690),
#                     [12:30,14:00] (750-840), [14:30,15:00] (870-900), [15:30,16:00] (930-960).
# Julia’s free Friday:
#   [10:00,10:30] (600-630), [11:30,12:30] (690-750),
#   [14:00,14:30] (840-870), [15:00,15:30] (900-930), [16:00,17:00] (960-1020).
#
# The only one-hour contiguous overlap comes from:
#   Brian’s [11:00,13:00] (660-780) intersected with Julia’s [11:30,12:30] (690-750).
#   The intersection is [690,750]. To have a full 60-minute meeting, start must satisfy:
#       start >= 690 and start + 60 <= 750, i.e. start <=690.
#   So the only possibility is start = 690 (which is 11:30) with meeting ending at 690+60 = 750 (12:30).
interval_friday = (start == 690)

# Add the conditional constraints:
constraints.append(Implies(day == 1, interval_tuesday))
constraints.append(Implies(day == 2, interval_wednesday))
constraints.append(Implies(day == 3, interval_thursday))
constraints.append(Implies(day == 4, interval_friday))
# (We also add Monday, though Brian prefers to avoid it.)
# constraints.append(Implies(day == 0, Or(start == 600, start == 870, start == 960))) 

# Use Optimize so we can choose the earliest available slot (minimizing a combined metric)
opt = Optimize()
for c in constraints:
    opt.add(c)

# Our objective is to schedule at the earliest time in the week. We can combine day and start into one number.
# (Since Monday is excluded, the earliest possible day is Tuesday (1).)
opt.minimize(day * 10000 + start)

if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    
    # Convert minutes to HH:MM format
    start_hour = chosen_start // 60
    start_min = chosen_start % 60
    end_time = chosen_start + 60
    end_hour = end_time // 60
    end_min = end_time % 60
    
    print("SOLUTION:")
    print("Day:", day_names[chosen_day])
    print("Start Time: {:02d}:{:02d}".format(start_hour, start_min))
    print("End Time: {:02d}:{:02d}".format(end_hour, end_min))
else:
    print("No solution found")