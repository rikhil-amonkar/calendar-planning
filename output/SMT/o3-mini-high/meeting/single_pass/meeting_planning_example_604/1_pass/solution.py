from z3 import *
import json

# Minutes-from-midnight constants for friend availabilities:
# William: 07:00 (420) to 09:00 (540)   -- unreachable since we start at 09:00 at Fisherman's Wharf
# Stephanie: 07:30 (450) to 09:30 (570)  -- unreachable for the same reason
# Joseph: 11:30 (690) to 12:45 (765), need >=15 minutes
# Karen: 14:30 (870) to 19:45 (1185), need >=30 minutes
# Kimberly: 15:45 (945) to 19:15 (1155), need >=30 minutes
# Laura: 19:45 (1185) to 21:30 (1290), need >=105 minutes (in fact, to meet her requirement you must spend her whole available window)
# Daniel: 21:15 (1275) to 21:45 (1305), need >=15 minutes

# Travel times (minutes) between locations (only the ones we need in our intended ordering):
# From Fisherman's Wharf (starting point at 09:00, i.e. 540) to Alamo Square (for Joseph): 20.
# From Alamo Square to Russian Hill (for Karen): 13.
# From Russian Hill to North Beach (for Kimberly): 5.
# Then, for the last meeting we have two branches:
#   • If meeting Laura (at The Castro), travel from North Beach to The Castro is 22 minutes.
#   • If meeting Daniel (at Golden Gate Park), travel from North Beach to Golden Gate Park is 22 minutes.

# We fix an ordering since the available windows force the order:
#   Fisherman's Wharf (start 09:00) -> Joseph -> Karen -> Kimberly -> (Laura OR Daniel)

# Create an Optimize object
opt = Optimize()

# Decision variables for meeting start times (expressed in minutes-from-midnight)
t_joseph   = Int("t_joseph")   # meeting at Alamo Square for Joseph
t_karen    = Int("t_karen")    # meeting at Russian Hill for Karen
t_kimberly = Int("t_kimberly") # meeting at North Beach for Kimberly
# For the last meeting we use a binary decision: choice==0 means choose Laura, choice==1 means choose Daniel.
choice = Int("choice")
opt.add(Or(choice == 0, choice == 1))

# For Daniel we create a start time variable. (Laura’s meeting is fixed by her available window.)
t_daniel = Int("t_daniel")

# Meeting durations (in minutes)
duration_joseph   = 15
duration_karen    = 30
duration_kimberly = 30
duration_daniel   = 15
duration_laura    = 105  # fixed: must cover her full availability

# ----------------------------
# Add time-window constraints for each meeting:
# Joseph: available 11:30 (690) to 12:45 (765); meeting lasts 15 minutes so start must be <=750.
opt.add(t_joseph >= 690, t_joseph <= 750)
# Karen: available 14:30 (870) to 19:45 (1185); meeting lasts 30 so start must be <= 1185-30 = 1155.
opt.add(t_karen >= 870, t_karen <= 1155)
# Kimberly: available 15:45 (945) to 19:15 (1155); meeting lasts 30 so start must be <= 1155-30 = 1125.
opt.add(t_kimberly >= 945, t_kimberly <= 1125)
# Daniel (if chosen): available 21:15 (1275) to (1305-15) = 1290.
opt.add(t_daniel >= 1275, t_daniel <= 1290)

# ----------------------------
# Add travel constraints between meetings.
# From Fisherman's Wharf (9:00 = 540) to Joseph at Alamo Square (travel=20 min):
# By availability, t_joseph >= 540+20 = 560; but Joseph's start is already bounded below by 690.
# From Joseph to Karen:
# Joseph meeting lasts 15 minutes. Travel from Alamo Square to Russian Hill = 13 minutes.
# So:  t_karen >= t_joseph + 15 + 13.
opt.add(t_karen >= t_joseph + 28)
# From Karen to Kimberly:
# Karen meeting lasts 30 minutes. Travel from Russian Hill to North Beach = 5.
# So:  t_kimberly >= t_karen + 30 + 5.
opt.add(t_kimberly >= t_karen + 35)

# ----------------------------
# Last meeting branch:
# (a) If choice==0 (Laura is chosen):
#     Then Laura’s meeting is fixed: It must take place in her entire window, i.e.
#     start at 19:45 (1185) and end at 21:30 (1290).
#     Also, travel from Kimberly (North Beach) to The Castro (Laura) is 22 minutes,
#     so we require that 1185 >= (t_kimberly + 30 + 22)  i.e. t_kimberly <= 1185 - 52 = 1133.
opt.add(If(choice == 0, t_kimberly <= 1133, True))
# (b) If choice==1 (Daniel is chosen):
#     Then his meeting must obey the travel from Kimberly: travel from North Beach to Golden Gate Park = 22 minutes.
#     Kimberly’s meeting lasts 30 minutes so we require:
#         t_daniel >= (t_kimberly + 30 + 22)  i.e. t_daniel >= t_kimberly + 52.
opt.add(If(choice == 1, t_daniel >= t_kimberly + 52, True))
# And in either branch, enforce that the meeting’s end time is within the friend’s window.
# For Daniel: meeting lasts 15 minutes so: t_daniel + 15 <= 1305.
opt.add(If(choice == 1, t_daniel + 15 <= 1305, True))
# (For Laura, the meeting times are fixed by her window.)

# ----------------------------
# Optionally, add an objective to “finish” as early as possible.
# The finish time of the last meeting is:
#    if Laura: fixed end 1290, or if Daniel: t_daniel+15.
finish_time = If(choice == 0, 1290, t_daniel + 15)
opt.minimize(finish_time)

# ----------------------------
# Solve and output the itinerary in the required JSON format.
if opt.check() == sat:
    m = opt.model()
    # Extract meeting start times (and compute end times by adding the fixed duration).
    joseph_start   = m[t_joseph].as_long()
    joseph_end     = joseph_start + duration_joseph
    karen_start    = m[t_karen].as_long()
    karen_end      = karen_start + duration_karen
    kimberly_start = m[t_kimberly].as_long()
    kimberly_end   = kimberly_start + duration_kimberly

    chosen = m[choice].as_long()  # 0 means Laura; 1 means Daniel

    def minutes_to_str(m_val):
        h = m_val // 60
        minute = m_val % 60
        return f"{h:02d}:{minute:02d}"

    itinerary = []
    itinerary.append({"action": "meet", "person": "Joseph",
                      "start_time": minutes_to_str(joseph_start),
                      "end_time": minutes_to_str(joseph_end)})
    itinerary.append({"action": "meet", "person": "Karen",
                      "start_time": minutes_to_str(karen_start),
                      "end_time": minutes_to_str(karen_end)})
    itinerary.append({"action": "meet", "person": "Kimberly",
                      "start_time": minutes_to_str(kimberly_start),
                      "end_time": minutes_to_str(kimberly_end)})
    
    if chosen == 0:
        # If Laura is chosen then her meeting is fixed:
        itinerary.append({"action": "meet", "person": "Laura",
                          "start_time": "19:45", "end_time": "21:30"})
    else:
        daniel_start = m[t_daniel].as_long()
        daniel_end = daniel_start + duration_daniel
        itinerary.append({"action": "meet", "person": "Daniel",
                          "start_time": minutes_to_str(daniel_start),
                          "end_time": minutes_to_str(daniel_end)})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")