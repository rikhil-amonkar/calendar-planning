from z3 import *
import json

def minutes_to_str(m):
    # Convert minutes (since midnight) to HH:MM (24-hour format)
    hour = m // 60
    minute = m % 60
    return f"{hour:02d}:{minute:02d}"

# Create an Optimize object (to later pick a schedule that minimizes finishing time)
opt = Optimize()

# Define integer variables for meeting start and end times (minutes since midnight)
t_start = Int('t_start')  # Timothy meeting start (at Alamo Square)
t_end   = Int('t_end')    # Timothy meeting end

m_start = Int('m_start')  # Mark meeting start (at Presidio)
m_end   = Int('m_end')    # Mark meeting end

j_start = Int('j_start')  # Joseph meeting start (at Russian Hill)
j_end   = Int('j_end')    # Joseph meeting end

# Define a Boolean variable to choose the order for the later two meetings.
# order0 = True means: Timothy → Joseph → Mark.
# order0 = False means: Timothy → Mark → Joseph.
order0 = Bool('order0')

# -----------------------
# Set availability constraints
# -----------------------
# You arrive at Golden Gate Park at 9:00AM (9:00 = 540 minutes) and must travel to Alamo Square (10 minutes).
# Timothy is at Alamo Square from 12:00 (720) to 16:15 (975). Minimum meeting time is 105 minutes.
opt.add(t_start >= 720)       # Cannot start before 12:00
opt.add(t_end <= 975)         # Must finish by 16:15
opt.add(t_end - t_start >= 105)

# Mark is at Presidio from 18:45 (1125) to 21:00 (1260). Minimum meeting time is 60 minutes.
opt.add(m_start >= 1125)
opt.add(m_end <= 1260)
opt.add(m_end - m_start >= 60)

# Joseph is at Russian Hill from 16:45 (1005) to 21:30 (1290). Minimum meeting time is 60 minutes.
opt.add(j_start >= 1005)
opt.add(j_end <= 1290)
opt.add(j_end - j_start >= 60)

# Also, ensure that you leave Golden Gate Park at 9:00 and take 10 minutes to get to Alamo Square.
# (Since 540 + 10 = 550, but t_start is already constrained to be at least 720.)
opt.add(t_start >= 540 + 10)

# -----------------------
# Add travel constraints for the order segments.
# Travel times (in minutes):
#  • Golden Gate Park → Alamo Square: 10
#  • Alamo Square → Russian Hill: 13
#  • Alamo Square → Presidio: 18
#  • Russian Hill → Presidio: 14
#  • Presidio → Russian Hill: 14
#
# Since Timothy is at Alamo Square, we now decide the order of the other meetings.
# -----------------------
# If order0 is True, then the schedule is:
#   Timothy (Alamo Square)  → travel (13) → Joseph (Russian Hill) → travel (14) → Mark (Presidio)
#
# Else (order0 False), the schedule is:
#   Timothy (Alamo Square) → travel (18) → Mark (Presidio) → travel (14) → Joseph (Russian Hill)
opt.add(If(order0,
           And(t_end + 13 <= j_start,   # travel from Alamo to Russian Hill
               j_end + 14 <= m_start),  # travel from Russian Hill to Presidio
           And(t_end + 18 <= m_start,   # travel from Alamo to Presidio
               m_end + 14 <= j_start))) # travel from Presidio to Russian Hill

# -----------------------
# To “optimize your goals”, we try to leave as early as possible.
# Define the finish time of the last meeting, which depends on the order.
# If order0 is True then the last meeting is Mark (m_end), else it is Joseph (j_end).
final_finish = If(order0, m_end, j_end)
opt.minimize(final_finish)

# -----------------------
# Solve the schedule
# -----------------------
if opt.check() == sat:
    model = opt.model()
    # Get the meeting times as integers
    T_start = model[t_start].as_long()
    T_end   = model[t_end].as_long()
    M_start = model[m_start].as_long()
    M_end   = model[m_end].as_long()
    J_start = model[j_start].as_long()
    J_end   = model[j_end].as_long()
    order_val = is_true(model.evaluate(order0))
    
    itinerary = []
    # Timothy meeting (at Alamo Square) is always first.
    itinerary.append({
        "action": "meet",
        "person": "Timothy",
        "start_time": minutes_to_str(T_start),
        "end_time": minutes_to_str(T_end)
    })
    
    # Depending on the chosen order, add the remaining meetings in order.
    if order_val:
        # Order: Timothy → Joseph → Mark
        itinerary.append({
            "action": "meet",
            "person": "Joseph",
            "start_time": minutes_to_str(J_start),
            "end_time": minutes_to_str(J_end)
        })
        itinerary.append({
            "action": "meet",
            "person": "Mark",
            "start_time": minutes_to_str(M_start),
            "end_time": minutes_to_str(M_end)
        })
    else:
        # Order: Timothy → Mark → Joseph
        itinerary.append({
            "action": "meet",
            "person": "Mark",
            "start_time": minutes_to_str(M_start),
            "end_time": minutes_to_str(M_end)
        })
        itinerary.append({
            "action": "meet",
            "person": "Joseph",
            "start_time": minutes_to_str(J_start),
            "end_time": minutes_to_str(J_end)
        })
    
    # Output the itinerary as a JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")