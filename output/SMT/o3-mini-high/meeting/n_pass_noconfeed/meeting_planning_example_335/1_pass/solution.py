import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, sat

def to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()
    # Decision variables for meeting start times (in minutes after midnight)
    s_H = Int('s_H')  # Helen's meeting start at North Beach
    s_K = Int('s_K')  # Kevin's meeting start at Mission District
    s_B = Int('s_B')  # Betty's meeting start at Financial District
    s_A = Int('s_A')  # Amanda's meeting start at Alamo Square

    # Boolean variables indicating whether a meeting is scheduled
    sched_H = Bool('sched_H')
    sched_K = Bool('sched_K')
    sched_B = Bool('sched_B')
    sched_A = Bool('sched_A')
    
    # Fixed meeting durations (in minutes)
    d_H = 15   # Helen needs at least 15 minutes
    d_K = 45   # Kevin needs at least 45 minutes
    d_B = 90   # Betty needs at least 90 minutes
    d_A = 60   # Amanda needs at least 60 minutes

    # Define travel time matrix using location indices:
    # 0: Pacific Heights (starting point)
    # 1: North Beach (Helen)
    # 2: Financial District (Betty)
    # 3: Alamo Square (Amanda)
    # 4: Mission District (Kevin)
    travel = {
        (0,1): 9,  (0,2): 13, (0,3): 10, (0,4): 15,
        (1,0): 8,  (1,2): 8,  (1,3): 16, (1,4): 18,
        (2,0): 13, (2,1): 7,  (2,3): 17, (2,4): 17,
        (3,0): 10, (3,1): 15, (3,2): 17, (3,4): 10,
        (4,0): 16, (4,1): 17, (4,2): 17, (4,3): 11,
    }
    
    # Basic domain constraints: assume times between 0 and 1440 (i.e. within one day)
    opt.add(s_H >= 0, s_H <= 1440)
    opt.add(s_K >= 0, s_K <= 1440)
    opt.add(s_B >= 0, s_B <= 1440)
    opt.add(s_A >= 0, s_A <= 1440)

    # Availability window constraints (only active if the meeting is scheduled)
    # Helen is available at North Beach from 9:00 (540) to 17:00 (1020)
    opt.add(If(sched_H, And(s_H >= 540, s_H + d_H <= 1020), True))
    # Kevin is available at Mission District from 10:45 (645) to 14:45 (885)
    opt.add(If(sched_K, And(s_K >= 645, s_K + d_K <= 885), True))
    # Betty is available at Financial District from 19:00 (1140) to 21:45 (1305)
    opt.add(If(sched_B, And(s_B >= 1140, s_B + d_B <= 1305), True))
    # Amanda is available at Alamo Square from 19:45 (1185) to 21:00 (1260)
    opt.add(If(sched_A, And(s_A >= 1185, s_A + d_A <= 1260), True))
    
    # Morning meetings: Helen and Kevin.
    # They must start after arriving at the first meeting location.
    # If only one is scheduled, its start must be at least (9:00 + travel time from Pacific Heights).
    opt.add(If(And(sched_H, Not(sched_K)),
               s_H >= 540 + travel[(0,1)],
               True))
    opt.add(If(And(sched_K, Not(sched_H)),
               s_K >= 540 + travel[(0,4)],
               True))
    # If both are scheduled, enforce a disjunctive ordering with travel time between them.
    opt.add(If(And(sched_H, sched_K),
               Or(
                   And(s_H <= s_K,
                       s_H >= 540 + travel[(0,1)],
                       s_K >= s_H + d_H + travel[(1,4)]),
                   And(s_K < s_H,
                       s_K >= 540 + travel[(0,4)],
                       s_H >= s_K + d_K + travel[(4,1)])
               ),
               True))
    
    # Define auxiliary expressions for the morning block:
    # morning_end: the finish time of the last meeting in the morning.
    # If both scheduled, then if Helen comes first then morning_end = s_K + d_K,
    # else if Kevin comes first then morning_end = s_H + d_H.
    morning_end = If(And(sched_H, sched_K),
                     If(s_H <= s_K, s_K + d_K, s_H + d_H),
                     If(sched_H,
                        s_H + d_H,
                        If(sched_K, s_K + d_K, 540)))
    
    # morning_last_loc: the location index from which you depart for the evening.
    # If both are scheduled, the last meeting’s location is determined by the ordering.
    morning_last_loc = If(And(sched_H, sched_K),
                          If(s_H <= s_K, 4, 1),
                          If(sched_H, 1,
                             If(sched_K, 4, 0)))
    
    # Evening meeting travel constraints: the start time must account for travel from the last morning location.
    # For Betty (Financial District, index 2)
    opt.add(If(sched_B,
               s_B >= morning_end +
                     If(Or(sched_H, sched_K),
                        If(And(sched_H, sched_K),
                           If(s_H <= s_K, travel[(4,2)], travel[(1,2)]),
                           If(sched_H, travel[(1,2)], travel[(4,2)])),
                        travel[(0,2)]),
               True))
    # For Amanda (Alamo Square, index 3)
    opt.add(If(sched_A,
               s_A >= morning_end +
                     If(Or(sched_H, sched_K),
                        If(And(sched_H, sched_K),
                           If(s_H <= s_K, travel[(4,3)], travel[(1,3)]),
                           If(sched_H, travel[(1,3)], travel[(4,3)])),
                        travel[(0,3)]),
               True))
    
    # At most one evening meeting can be scheduled (they conflict due to tight windows)
    opt.add((If(sched_B, 1, 0) + If(sched_A, 1, 0)) <= 1)
    
    # Objective: maximize the total number of meetings scheduled.
    total_meetings = If(sched_H, 1, 0) + If(sched_K, 1, 0) + If(sched_B, 1, 0) + If(sched_A, 1, 0)
    opt.maximize(total_meetings)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        meetings = []
        # If a meeting is scheduled, get its start and computed end times.
        if model.evaluate(sched_H):
            start = model.evaluate(s_H).as_long()
            end = start + d_H
            meetings.append(("Helen", "North Beach", start, end))
        if model.evaluate(sched_K):
            start = model.evaluate(s_K).as_long()
            end = start + d_K
            meetings.append(("Kevin", "Mission District", start, end))
        if model.evaluate(sched_B):
            start = model.evaluate(s_B).as_long()
            end = start + d_B
            meetings.append(("Betty", "Financial District", start, end))
        if model.evaluate(sched_A):
            start = model.evaluate(s_A).as_long()
            end = start + d_A
            meetings.append(("Amanda", "Alamo Square", start, end))
        
        # Sort meetings by start time so the itinerary is in chronological order.
        meetings.sort(key=lambda x: x[2])
        
        itinerary = []
        for person, location, start, end in meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": to_time_str(start),
                "end_time": to_time_str(end)
            })
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()