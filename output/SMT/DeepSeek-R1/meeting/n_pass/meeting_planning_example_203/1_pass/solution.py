from z3 import *
import json

def main():
    # Travel times matrix: [from][to]
    # Locations: Financial District (0), Fisherman's Wharf (1), Pacific Heights (2), Mission District (3)
    travel = [
        [0, 10, 13, 17],   # From Financial District
        [11, 0, 12, 22],    # From Fisherman's Wharf
        [13, 13, 0, 15],    # From Pacific Heights
        [17, 22, 16, 0]     # From Mission District
    ]
    
    # Create the optimizer
    opt = Optimize()
    
    # Boolean variables for whether we meet each friend
    meet_d = Bool('meet_d')
    meet_t = Bool('meet_t')
    meet_r = Bool('meet_r')
    
    # Start times in minutes after 9:00 AM (integer variables)
    T_d = Int('T_d')
    T_t = Int('T_t')
    T_r = Int('T_r')
    
    # Position of each meeting in the itinerary (0 means not meeting)
    P_d = Int('P_d')
    P_t = Int('P_t')
    P_r = Int('P_r')
    
    # Durations of meetings in minutes
    dur_d = 15
    dur_t = 75
    dur_r = 90
    
    # Availability constraints
    # David: 10:45 AM (105 min) to 3:30 PM (390 min)
    opt.add(Implies(meet_d, And(T_d >= 105, T_d + dur_d <= 390)))
    # Timothy: 9:00 AM (0 min) to 3:30 PM (390 min)
    opt.add(Implies(meet_t, And(T_t >= 0, T_t + dur_t <= 390)))
    # Robert: 12:15 PM (195 min) to 7:45 PM (645 min)
    opt.add(Implies(meet_r, And(T_r >= 195, T_r + dur_r <= 645)))
    
    # Position constraints: if meeting happens, position is between 1 and 3; else 0.
    opt.add(Implies(meet_d, And(P_d >= 1, P_d <= 3)))
    opt.add(Implies(meet_t, And(P_t >= 1, P_t <= 3)))
    opt.add(Implies(meet_r, And(P_r >= 1, P_r <= 3)))
    opt.add(Implies(Not(meet_d), P_d == 0))
    opt.add(Implies(Not(meet_t), P_t == 0))
    opt.add(Implies(Not(meet_r), P_r == 0))
    
    # Distinct positions for meetings that happen
    opt.add(Implies(And(meet_d, meet_t), P_d != P_t))
    opt.add(Implies(And(meet_d, meet_r), P_d != P_r))
    opt.add(Implies(And(meet_t, meet_r), P_t != P_r))
    
    # For a meeting at position > 1, there must be a meeting at position-1
    opt.add(Implies(And(meet_d, P_d > 1), 
                   Or(And(meet_t, P_t == P_d - 1), 
                      And(meet_r, P_r == P_d - 1))))
    opt.add(Implies(And(meet_t, P_t > 1), 
                   Or(And(meet_d, P_d == P_t - 1), 
                      And(meet_r, P_r == P_t - 1))))
    opt.add(Implies(And(meet_r, P_r > 1), 
                   Or(And(meet_d, P_d == P_r - 1), 
                      And(meet_t, P_t == P_r - 1))))
    
    # First meeting: must start after travel from Financial District (location 0)
    opt.add(Implies(And(meet_d, P_d == 1), T_d >= travel[0][1]))
    opt.add(Implies(And(meet_t, P_t == 1), T_t >= travel[0][2]))
    opt.add(Implies(And(meet_r, P_r == 1), T_r >= travel[0][3]))
    
    # Subsequent meetings: must start after previous meeting ends plus travel
    opt.add(Implies(And(meet_d, P_d > 1),
                   Or(
                      And(meet_t, P_t == P_d - 1, T_d >= T_t + dur_t + travel[2][1]),
                      And(meet_r, P_r == P_d - 1, T_d >= T_r + dur_r + travel[3][1])
                   )))
    opt.add(Implies(And(meet_t, P_t > 1),
                   Or(
                      And(meet_d, P_d == P_t - 1, T_t >= T_d + dur_d + travel[1][2]),
                      And(meet_r, P_r == P_t - 1, T_t >= T_r + dur_r + travel[3][2])
                   )))
    opt.add(Implies(And(meet_r, P_r > 1),
                   Or(
                      And(meet_d, P_d == P_r - 1, T_r >= T_d + dur_d + travel[1][3]),
                      And(meet_t, P_t == P_r - 1, T_r >= T_t + dur_t + travel[2][3])
                   )))
    
    # Maximize the number of meetings
    num_meetings = If(meet_d, 1, 0) + If(meet_t, 1, 0) + If(meet_r, 1, 0)
    opt.maximize(num_meetings)
    
    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        meetings = []
        # Check and add David's meeting
        if is_true(m.evaluate(meet_d)):
            start_d = m.evaluate(T_d).as_long()
            meetings.append(("David", start_d, start_d + dur_d))
        # Check and add Timothy's meeting
        if is_true(m.evaluate(meet_t)):
            start_t = m.evaluate(T_t).as_long()
            meetings.append(("Timothy", start_t, start_t + dur_t))
        # Check and add Robert's meeting
        if is_true(m.evaluate(meet_r)):
            start_r = m.evaluate(T_r).as_long()
            meetings.append(("Robert", start_r, start_r + dur_r))
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[1])
        
        # Convert to itinerary in JSON format
        itinerary = []
        for (person, start_minutes, end_minutes) in meetings:
            # Convert start_minutes to time string
            start_hour = 9 + start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = 9 + end_minutes // 60
            end_minute = end_minutes % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
        
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()