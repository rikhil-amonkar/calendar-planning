from z3 import *
import json

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Scenario 1: Castro -> Mission -> Financial
s1 = Solver()
L_start_s1 = Int('L_start_s1')
A_start_s1 = Int('A_start_s1')

# Laura's constraints
s1.add(L_start_s1 >= 735)
s1.add(L_start_s1 + 75 <= 1185)

# Anthony's constraints based on scenario 1
arrival_financial_s1 = L_start_s1 + 75 + 17
s1.add(A_start_s1 >= arrival_financial_s1)
s1.add(A_start_s1 >= 750)
s1.add(A_start_s1 + 30 <= 885)

# Scenario 2: Castro -> Financial -> Mission
s2 = Solver()
A_start_s2 = Int('A_start_s2')
L_start_s2 = Int('L_start_s2')

# Anthony's constraints
s2.add(A_start_s2 >= 750)
s2.add(A_start_s2 + 30 <= 885)

# Laura's constraints based on scenario 2
arrival_mission_s2 = A_start_s2 + 30 + 17
s2.add(L_start_s2 >= arrival_mission_s2)
s2.add(L_start_s2 >= 735)
s2.add(L_start_s2 + 75 <= 1185)

# Check scenarios
if s1.check() == sat:
    m = s1.model()
    l_start = m[L_start_s1].as_long()
    a_start = m[A_start_s1].as_long()
    # Laura meeting
    l_start_time = to_time(l_start)
    l_end_time = to_time(l_start + 75)
    # Anthony meeting
    a_start_time = to_time(a_start)
    a_end_time = to_time(a_start + 30)
    itinerary = [
        {"action": "meet", "person": "Laura", "start_time": l_start_time, "end_time": l_end_time},
        {"action": "meet", "person": "Anthony", "start_time": a_start_time, "end_time": a_end_time}
    ]
elif s2.check() == sat:
    m = s2.model()
    a_start = m[A_start_s2].as_long()
    l_start = m[L_start_s2].as_long()
    # Anthony meeting
    a_start_time = to_time(a_start)
    a_end_time = to_time(a_start + 30)
    # Laura meeting
    l_start_time = to_time(l_start)
    l_end_time = to_time(l_start + 75)
    itinerary = [
        {"action": "meet", "person": "Anthony", "start_time": a_start_time, "end_time": a_end_time},
        {"action": "meet", "person": "Laura", "start_time": l_start_time, "end_time": l_end_time}
    ]
else:
    # No solution found, but according to manual analysis, there should be
    itinerary = []

# Output the JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))