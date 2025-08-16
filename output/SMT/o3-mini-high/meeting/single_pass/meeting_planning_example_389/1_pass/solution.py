from z3 import *
import json

# Create an optimizer instance
opt = Optimize()

# ---- Decision Variables ----
# Boolean variables representing whether we schedule the meeting with each friend.
m = Bool('m')  # Mary at Richmond District
s = Bool('s')  # Sarah at Fisherman's Wharf
t = Bool('t')  # Thomas at Bayview
h = Bool('h')  # Helen at Mission District

# Integer variables for the start times (in minutes from midnight).
# We use minutes so that (e.g.) 9:00 AM is 540, 13:00 is 780, etc.
m_start = Int('m_start')
s_start = Int('s_start')
t_start = Int('t_start')
h_start = Int('h_start')

# ---- Known meeting durations (minutes) ----
m_duration = 75   # Mary
s_duration = 105  # Sarah
t_duration = 120  # Thomas
h_duration = 30   # Helen

# ---- Availability Windows (in minutes from midnight) ----
# Mary: available 13:00 (780) to 19:15 (1155) [meeting must finish by 1155]
opt.add(Implies(m, m_start >= 780))
opt.add(Implies(m, m_start + m_duration <= 1155))

# Sarah: available 14:45 (885) to 17:30 (1050)
opt.add(Implies(s, s_start >= 885))
opt.add(Implies(s, s_start + s_duration <= 1050))

# Thomas: available 15:15 (915) to 18:45 (1125)
opt.add(Implies(t, t_start >= 915))
opt.add(Implies(t, t_start + t_duration <= 1125))

# Helen: available 21:45 (1305) to 22:30 (1350)
opt.add(Implies(h, h_start >= 1305))
opt.add(Implies(h, h_start + h_duration <= 1350))

# ---- Travel Times (in minutes) ----
# Given travel-times between Districts:
# From Haight-Ashbury (starting location at 9:00, i.e. 540) our travel times are:
#   Haight-Ashbury -> Richmond District: 10
#   Haight-Ashbury -> Fisherman's Wharf: 23
#   Haight-Ashbury -> Bayview: 18
#   Haight-Ashbury -> Mission District: 11
#
# And between meeting locations:
#   Richmond -> Fisherman's Wharf: 18
#   Richmond -> Bayview: 26
#   Richmond -> Mission: 20
#   Fisherman's Wharf -> Mission: 22
#   Bayview -> Mission: 13

# (Since the availability lower bounds are set well after the travel-from-start,
#  we do not need extra constraints for travel from Haight-Ashbury.)

# ---- Ordering Constraints ----
# We are going to “force” a fixed order when more than one meeting is scheduled.
# Because our analysis shows that meeting Sarah and Thomas together is not possible,
# our model adds the constraint that at most one of them can be scheduled.
opt.add(Or(Not(s), Not(t)))  # Cannot schedule both Sarah and Thomas.

# When Mary is used along with Sarah or Thomas, Mary must be visited first.
# -- Mary then Sarah: travel from Richmond to Fisherman's Wharf takes 18 minutes.
opt.add(Implies(And(m, s), s_start >= m_start + m_duration + 18))
# -- Mary then Thomas: travel from Richmond to Bayview takes 26 minutes.
opt.add(Implies(And(m, t), t_start >= m_start + m_duration + 26))

# When a second (midday) meeting is scheduled and then Helen is also scheduled, Helen must be reached after.
# If Sarah is the second meeting:
opt.add(Implies(And(s, h), h_start >= s_start + s_duration + 22))  # Fisherman's Wharf -> Mission: 22 minutes
# If Thomas is the second meeting:
opt.add(Implies(And(t, h), h_start >= t_start + t_duration + 13))  # Bayview -> Mission: 13 minutes

# If only Mary and Helen are scheduled (i.e. no Sarah/Thomas), then travel from Richmond to Mission is 20 minutes.
opt.add(Implies(And(m, h, Not(s), Not(t)), h_start >= m_start + m_duration + 20))

# (For any meeting scheduled on its own, the availability constraints already “force” the appropriate start times.)

# ---- Objective ----
# We want to maximize the number of meetings scheduled (i.e. meet as many friends as possible).
# In case of a tie, we give a small bonus for extra meeting minutes.
sched_count = If(m, 1, 0) + If(s, 1, 0) + If(t, 1, 0) + If(h, 1, 0)
total_meeting_minutes = If(m, m_duration, 0) + If(s, s_duration, 0) + If(t, t_duration, 0) + If(h, h_duration, 0)
# Combining with a high weight on count ensures that a solution with 3 meetings is preferred to one with 2, etc.
opt.maximize(1000 * sched_count + total_meeting_minutes)

# ---- Solve the model ----
if opt.check() == sat:
    model = opt.model()
else:
    print("No solution found!")
    exit(1)

# ---- Helper: convert minutes to HH:MM string ----
def minutes_to_time_str(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

# ---- Build the itinerary based on scheduled meetings ----
itinerary = []
if is_true(model.evaluate(m)):
    m_start_val = model.evaluate(m_start).as_long()
    m_end_val = m_start_val + m_duration
    itinerary.append({
        "action": "meet",
        "person": "Mary",
        "start_time": minutes_to_time_str(m_start_val),
        "end_time": minutes_to_time_str(m_end_val)
    })
    
if is_true(model.evaluate(s)):
    s_start_val = model.evaluate(s_start).as_long()
    s_end_val = s_start_val + s_duration
    itinerary.append({
        "action": "meet",
        "person": "Sarah",
        "start_time": minutes_to_time_str(s_start_val),
        "end_time": minutes_to_time_str(s_end_val)
    })
    
if is_true(model.evaluate(t)):
    t_start_val = model.evaluate(t_start).as_long()
    t_end_val = t_start_val + t_duration
    itinerary.append({
        "action": "meet",
        "person": "Thomas",
        "start_time": minutes_to_time_str(t_start_val),
        "end_time": minutes_to_time_str(t_end_val)
    })
    
if is_true(model.evaluate(h)):
    h_start_val = model.evaluate(h_start).as_long()
    h_end_val = h_start_val + h_duration
    itinerary.append({
        "action": "meet",
        "person": "Helen",
        "start_time": minutes_to_time_str(h_start_val),
        "end_time": minutes_to_time_str(h_end_val)
    })

output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))