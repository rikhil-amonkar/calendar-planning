from z3 import *
import json

def main():
    # Define travel times between locations (in minutes)
    travel = {
        ('FW', 'GGP'): 25,  # From Free Water to Golden Gate Park
        ('FW', 'P'): 17,     # From Free Water to Presidio
        ('FW', 'RD'): 18,    # From Free Water to Richmond District
        ('GGP', 'FW'): 24,   # Return trip times
        ('GGP', 'P'): 11,
        ('GGP', 'RD'): 7,
        ('P', 'FW'): 19,
        ('P', 'GGP'): 12,
        ('P', 'RD'): 7,
        ('RD', 'FW'): 18,
        ('RD', 'GGP'): 9,
        ('RD', 'P'): 7
    }
    
    # Meeting start time variables and existence booleans
    s_M, s_N, s_E = Ints('s_M s_N s_E')
    meet_M, meet_N, meet_E = Bools('meet_M meet_N meet_E')
    
    # Meeting durations (minutes)
    dur_M = 15   # Melissa
    dur_N = 105  # Nancy
    dur_E = 120  # Emily
    
    # Constraints list
    constraints = []
    
    # Starting at Free Water (FW) at 9:00 AM (540 minutes from midnight)
    start_FW = 540
    
    # Availability windows (minutes from midnight)
    # Melissa: 8:30 AM (510) to 8:00 PM (1200)
    constraints.append(Implies(meet_M, And(
        s_M >= start_FW + travel[('FW','GGP')],
        s_M >= 510,
        s_M + dur_M <= 1200
    )))
    
    # Nancy: 7:45 PM (1185) to 10:00 PM (1320)
    constraints.append(Implies(meet_N, And(
        s_N >= start_FW + travel[('FW','P')],
        s_N >= 1185,
        s_N + dur_N <= 1320
    )))
    
    # Emily: 4:45 PM (1005) to 10:00 PM (1320)
    constraints.append(Implies(meet_E, And(
        s_E >= start_FW + travel[('FW','RD')],
        s_E >= 1005,
        s_E + dur_E <= 1320
    )))
    
    # Pairwise meeting constraints with correct location pairs
    constraints.append(Implies(And(meet_M, meet_N), Or(
        s_N >= s_M + dur_M + travel[('GGP','P')],
        s_M >= s_N + dur_N + travel[('P','GGP')]
    )))
    
    constraints.append(Implies(And(meet_M, meet_E), Or(
        s_E >= s_M + dur_M + travel[('GGP','RD')],
        s_M >= s_E + dur_E + travel[('RD','GGP')]
    )))
    
    constraints.append(Implies(And(meet_N, meet_E), Or(
        s_E >= s_N + dur_N + travel[('P','RD')],
        s_N >= s_E + dur_E + travel[('RD','P')]
    )))
    
    # Maximize number of meetings
    num_meetings = If(meet_M, 1, 0) + If(meet_N, 1, 0) + If(meet_E, 1, 0)
    
    # Solve with optimization
    s = Optimize()
    s.add(constraints)
    s.maximize(num_meetings)
    
    if s.check() == sat:
        m = s.model()
        meetings = []
        if is_true(m[meet_M]):
            start_val = m[s_M].as_long()
            meetings.append(("Melissa", start_val, dur_M))
        if is_true(m[meet_N]):
            start_val = m[s_N].as_long()
            meetings.append(("Nancy", start_val, dur_N))
        if is_true(m[meet_E]):
            start_val = m[s_E].as_long()
            meetings.append(("Emily", start_val, dur_E))
        
        # Format output
        itinerary = []
        for person, start, dur in sorted(meetings, key=lambda x: x[1]):
            end = start + dur
            start_str = f"{start//60:02d}:{start%60:02d}"
            end_str = f"{end//60:02d}:{end%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()