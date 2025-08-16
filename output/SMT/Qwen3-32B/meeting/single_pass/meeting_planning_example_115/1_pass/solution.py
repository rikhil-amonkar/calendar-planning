import json
from z3 import *

def to_minutes(hh, mm):
    return hh * 60 + mm

def to_time_str(m):
    h = m // 60
    m_min = m % 60
    return f"{h:02d}:{m_min:02d}"

solver = Solver()

start_carol = Int('start_carol')
end_carol = start_carol + 60
start_jessica = Int('start_jessica')
end_jessica = start_jessica + 45

D_RD = Int('D_RD')

# Scenario 1: Richmond -> Marina -> Pacific
solver.add(D_RD >= to_minutes(9, 0))  # 9:00 AM
arrival_marina = D_RD + 9
solver.add(start_carol >= arrival_marina)
solver.add(start_carol >= to_minutes(11, 30))  # 11:30 AM
solver.add(end_carol <= to_minutes(15, 0))  # 3:00 PM

arrival_pacific = end_carol + 7
solver.add(start_jessica >= arrival_pacific)
solver.add(start_jessica >= to_minutes(15, 30))  # 3:30 PM
solver.add(end_jessica <= to_minutes(16, 45))  # 4:45 PM

if solver.check() == sat:
    model = solver.model()
    sc = model[start_carol].as_long()
    sj = model[start_jessica].as_long()
    # Now build the JSON
    carol_start = to_time_str(sc)
    carol_end = to_time_str(sc + 60)
    jessica_start = to_time_str(sj)
    jessica_end = to_time_str(sj + 45)
    itinerary = [
        {"action": "meet", "person": "Carol", "start_time": carol_start, "end_time": carol_end},
        {"action": "meet", "person": "Jessica", "start_time": jessica_start, "end_time": jessica_end}
    ]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    # Scenario 2
    solver = Solver()
    start_carol = Int('start_carol')
    end_carol = start_carol + 60
    start_jessica = Int('start_jessica')
    end_jessica = start_jessica + 45

    D_RD2 = Int('D_RD2')  # Departure from Richmond to Pacific
    arrival_pacific2 = D_RD2 + 10
    D_PH = Int('D_PH')  # Departure from Pacific to Marina
    arrival_marina2 = D_PH + 6

    solver.add(D_RD2 >= to_minutes(9, 0))
    solver.add(D_PH >= arrival_pacific2)
    solver.add(start_carol >= arrival_marina2)
    solver.add(start_carol >= to_minutes(11, 30))
    solver.add(end_carol <= to_minutes(15, 0))
    arrival_pacific_again = end_carol + 7
    solver.add(start_jessica >= arrival_pacific_again)
    solver.add(start_jessica >= to_minutes(15, 30))
    solver.add(end_jessica <= to_minutes(16, 45))

    if solver.check() == sat:
        model = solver.model()
        sc = model[start_carol].as_long()
        sj = model[start_jessica].as_long()
        carol_start = to_time_str(sc)
        carol_end = to_time_str(sc + 60)
        jessica_start = to_time_str(sj)
        jessica_end = to_time_str(sj + 45)
        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": carol_start, "end_time": carol_end},
            {"action": "meet", "person": "Jessica", "start_time": jessica_start, "end_time": jessica_end}
        ]
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")