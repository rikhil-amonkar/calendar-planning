from z3 import *
import json

def minutes_to_time(m):
    # Convert integer minutes to H:MM (24-hour) format (no leading zero for hour)
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

# Constants (in minutes)
bayview_arrival = 9 * 60           # 9:00 -> 540
union_travel_from_bayview = 17     # Bayview to Union Square
presidio_travel_from_bayview = 31  # Bayview to Presidio
union_to_presidio = 24             # Union Square to Presidio
presidio_to_union = 22             # Presidio to Union Square
meeting_min = 120                  # minimum meeting duration in minutes

# Friend availability windows (in minutes from midnight)
richard_avail_start = 8 * 60 + 45  # 8:45 -> 525
richard_avail_end = 13 * 60        # 13:00 -> 780

charles_avail_start = 9 * 60 + 45  # 9:45 -> 585
charles_avail_end = 13 * 60        # 13:00 -> 780

# Create an Optimize solver instance
opt = Optimize()

# Decision variables for meeting times (minutes)
R_start = Int('R_start')  # Meeting start time with Richard at Union Square
R_end = Int('R_end')      # Meeting end time with Richard
C_start = Int('C_start')  # Meeting start time with Charles at Presidio
C_end = Int('C_end')      # Meeting end time with Charles

# Decision booleans: whether to schedule meeting for each friend.
attend_R = Bool('attend_R')
attend_C = Bool('attend_C')

# Boolean decision variable for ordering if both meetings are scheduled.
# If order_R_first is True then meet Richard first then Charles; if False then Charles first.
order_R_first = Bool('order_R_first')

# If a meeting is not scheduled, force its times to 0
opt.add(Implies(Not(attend_R), And(R_start == 0, R_end == 0)))
opt.add(Implies(Not(attend_C), And(C_start == 0, C_end == 0)))

# Constraints for meeting with Richard (at Union Square)
opt.add(Implies(attend_R, R_end - R_start >= meeting_min))
opt.add(Implies(attend_R, R_end <= richard_avail_end))
# For Richard, if he is the only meeting or comes first then R_start must be reachable from Bayview.
# Otherwise, if he is second (i.e. meeting with Charles occurs first), his start must be after finishing Charles.
opt.add(Implies(attend_R,
    And(
        R_start >= If(Or(Not(attend_C), order_R_first), bayview_arrival + union_travel_from_bayview, C_end + presidio_to_union),
        R_start >= richard_avail_start  # friend availability start (8:45)
    )
))

# Constraints for meeting with Charles (at Presidio)
opt.add(Implies(attend_C, C_end - C_start >= meeting_min))
opt.add(Implies(attend_C, C_end <= charles_avail_end))
# For Charles, if he is the only meeting or comes first then C_start must be reachable from Bayview.
# Otherwise, if he is second (Charles after Richard), his start must follow Richard's meeting.
opt.add(Implies(attend_C,
    And(
        C_start >= If(Or(Not(attend_R), Not(order_R_first)),
                      Max(bayview_arrival + presidio_travel_from_bayview, charles_avail_start),
                      R_end + union_to_presidio),
        C_start >= charles_avail_start  # friend availability start (9:45)
    )
))

# Additional ordering constraints when both meetings are scheduled.
# These constraints mirror the piecewise conditions above.
opt.add(Implies(And(attend_R, attend_C, order_R_first),
    And(
        # Richard is the first meeting: must be reachable directly.
        R_start >= bayview_arrival + union_travel_from_bayview,
        # Charles follows Richard: allow travel time from Union Square to Presidio.
        C_start >= R_end + union_to_presid o
    )
))
# For the other ordering (Charles first)
opt.add(Implies(And(attend_R, attend_C, Not(order_R_first)),
    And(
        # Charles is the first meeting: must be reachable directly.
        C_start >= Max(bayview_arrival + presidio_travel_from_bayview, charles_avail_start),
        # Richard follows Charles: allow travel time from Presidio to Union Square.
        R_start >= C_end + presidio_to_union
    )
))

# Define objective: maximize the number of meetings scheduled, then maximize total meeting duration.
meetings_count = If(attend_R, 1, 0) + If(attend_C, 1, 0)
total_duration = If(attend_R, R_end - R_start, 0) + If(attend_C, C_end - C_start, 0)
h1 = opt.maximize(meetings_count)
h2 = opt.maximize(total_duration)

# Check for a solution
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    # Determine which meetings are scheduled and in what order.
    has_R = is_true(model.evaluate(attend_R))
    has_C = is_true(model.evaluate(attend_C))
    if has_R and has_C:
        if is_true(model.evaluate(order_R_first)):
            itinerary.append({
                "action": "meet",
                "location": "Union Square",
                "person": "Richard",
                "start_time": minutes_to_time(model.evaluate(R_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(R_end).as_long())
            })
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Charles",
                "start_time": minutes_to_time(model.evaluate(C_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(C_end).as_long())
            })
        else:
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Charles",
                "start_time": minutes_to_time(model.evaluate(C_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(C_end).as_long())
            })
            itinerary.append({
                "action": "meet",
                "location": "Union Square",
                "person": "Richard",
                "start_time": minutes_to_time(model.evaluate(R_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(R_end).as_long())
            })
    elif has_R:
        itinerary.append({
            "action": "meet",
            "location": "Union Square",
            "person": "Richard",
            "start_time": minutes_to_time(model.evaluate(R_start).as_long()),
            "end_time": minutes_to_time(model.evaluate(R_end).as_long())
        })
    elif has_C:
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Charles",
            "start_time": minutes_to_time(model.evaluate(C_start).as_long()),
            "end_time": minutes_to_time(model.evaluate(C_end).as_long())
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))