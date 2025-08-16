from z3 import *
import json

# Conversion helper: minutes since midnight to "HH:MM" (24-hr format)
def minutes_to_time(m):
    hrs = m // 60
    mins = m % 60
    return f"{hrs:02d}:{mins:02d}"

# Meeting durations (in minutes)
dur_Richard = 30      # Richard must be met for at least 30 minutes.
dur_Kenneth  = 30      # Kenneth: 30 minutes.
dur_Sarah    = 90      # Sarah: 90 minutes.
dur_Karen    = 120     # Karen: 120 minutes.
dur_Daniel   = 15      # Daniel: 15 minutes.
dur_Mark     = 120     # Mark: 120 minutes.
dur_Mary     = 75      # Mary: 75 minutes.

# Time-window boundaries are given as minutes since midnight.
# For example: 9:00 AM is 9*60 = 540 minutes.
# Availability intervals (start_inclusive, end_inclusive for meeting end)
# Note: The meeting must finish by the given end.
availability = {
    "Richard": (8*60, 18*60 + 45),      # 08:00 to 18:45, meeting must finish by 18:45.
    "Kenneth": (11*60 +15, 19*60 +15),    # 11:15 to 19:15.
    "Sarah":   (11*60 +45, 14*60 +30),    # 11:45 to 14:30.
    "Karen":   (13*60 +15, 18*60 +30),     # 13:15 to 18:30.
    "Daniel":  (13*60 +45, 20*60 +30),     # 13:45 to 20:30.
    "Mark":    (17*60 +30, 21*60 +30),     # 17:30 to 21:30.
    "Mary":    (20*60, 21*60 +15)          # 20:00 to 21:15.
}

# Create Z3 Int variables representing the start time (in minutes) of each meeting.
# (Each meeting will run for exactly the minimum required duration.)
Richard  = Int("Richard")
Kenneth  = Int("Kenneth")
Sarah    = Int("Sarah")
Karen    = Int("Karen")
Daniel   = Int("Daniel")
Mark_v   = Int("Mark")
Mary     = Int("Mary")

solver = Solver()

# Our schedule starts at Nob Hill at 9:00 (540 minutes).
# The first meeting is with Richard at Chinatown.
# Constraint: travel from Nob Hill to Chinatown takes 6 minutes.
solver.add(Richard >= 540 + 6)
# Also, meeting must finish by the friend’s available end.
solver.add(Richard + dur_Richard <= availability["Richard"][1])
solver.add(Richard >= availability["Richard"][0])  # redundant if lower bound < 540+6

# Kenneth is at The Castro. He is available 11:15--19:15.
solver.add(Kenneth >= 11*60 + 15)
solver.add(Kenneth + dur_Kenneth <= availability["Kenneth"][1])

# Sarah is at Union Square. Available 11:45--14:30.
solver.add(Sarah >= 11*60 + 45)
solver.add(Sarah + dur_Sarah <= availability["Sarah"][1])

# Karen is at Russian Hill. Available 13:15--18:30.
solver.add(Karen >= 13*60 + 15)
solver.add(Karen + dur_Karen <= availability["Karen"][1])

# Daniel is at Pacific Heights. Available 13:45--20:30.
solver.add(Daniel >= 13*60 + 45)
solver.add(Daniel + dur_Daniel <= availability["Daniel"][1])

# Mark is at Golden Gate Park. Available 17:30--21:30.
solver.add(Mark_v >= 17*60 + 30)
solver.add(Mark_v + dur_Mark <= availability["Mark"][1])

# Mary is at Embarcadero. Available 20:00--21:15.
solver.add(Mary >= 20*60)
solver.add(Mary + dur_Mary <= availability["Mary"][1])

# Now add travel-time constraints between meetings.
# The meeting order (with locations) is chosen as:
# Nob Hill (start) -> Richard@Chinatown -> Kenneth@The Castro -> Sarah@Union Square
# -> Karen@Russian Hill -> Daniel@Pacific Heights -> Mark@Golden Gate Park -> Mary@Embarcadero.
#
# Travel times (in minutes) between locations (as given):
# Nob Hill to Chinatown: 6 minutes (already used above).
# Chinatown -> The Castro: 22 minutes.
solver.add(Richard + dur_Richard + 22 <= Kenneth)

# The Castro -> Union Square: 19 minutes.
solver.add(Kenneth + dur_Kenneth + 19 <= Sarah)

# Union Square -> Russian Hill: 13 minutes.
solver.add(Sarah + dur_Sarah + 13 <= Karen)

# Russian Hill -> Pacific Heights: 7 minutes.
solver.add(Karen + dur_Karen + 7 <= Daniel)

# Pacific Heights -> Golden Gate Park: 15 minutes.
solver.add(Daniel + dur_Daniel + 15 <= Mark_v)

# Golden Gate Park -> Embarcadero: 25 minutes.
solver.add(Mark_v + dur_Mark + 25 <= Mary)

# Solve for a feasible schedule.
if solver.check() == sat:
    model = solver.model()
    # Extract the meeting start times from the model.
    r_start = model[Richard].as_long()
    k_start = model[Kenneth].as_long()
    s_start = model[Sarah].as_long()
    ka_start = model[Karen].as_long()
    d_start = model[Daniel].as_long()
    m_start = model[Mark_v].as_long()
    ma_start = model[Mary].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "person": "Richard",
            "start_time": minutes_to_time(r_start),
            "end_time": minutes_to_time(r_start + dur_Richard)
        },
        {
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_time(k_start),
            "end_time": minutes_to_time(k_start + dur_Kenneth)
        },
        {
            "action": "meet",
            "person": "Sarah",
            "start_time": minutes_to_time(s_start),
            "end_time": minutes_to_time(s_start + dur_Sarah)
        },
        {
            "action": "meet",
            "person": "Karen",
            "start_time": minutes_to_time(ka_start),
            "end_time": minutes_to_time(ka_start + dur_Karen)
        },
        {
            "action": "meet",
            "person": "Daniel",
            "start_time": minutes_to_time(d_start),
            "end_time": minutes_to_time(d_start + dur_Daniel)
        },
        {
            "action": "meet",
            "person": "Mark",
            "start_time": minutes_to_time(m_start),
            "end_time": minutes_to_time(m_start + dur_Mark)
        },
        {
            "action": "meet",
            "person": "Mary",
            "start_time": minutes_to_time(ma_start),
            "end_time": minutes_to_time(ma_start + dur_Mary)
        }
    ]
    
    schedule = {"itinerary": itinerary}
    print(json.dumps(schedule, indent=4))
else:
    print("No solution found")