from z3 import *
import json

def main():
    # Define travel_time matrix (5x5) for indices: 
    # 0: Bayview (virtual start)
    # 1: Mary (Pacific Heights)
    # 2: Lisa (Mission District)
    # 3: Betty (Haight-Ashbury)
    # 4: Charles (Financial District)
    travel_time = [
        [0, 23, 13, 19, 19],
        [22, 0, 15, 11, 13],
        [15, 16, 0, 12, 17],
        [18, 12, 11, 0, 21],
        [19, 13, 17, 19, 0]
    ]
    
    # Durations for each meeting (index0 is virtual, duration 0)
    dur = [0, 45, 75, 90, 120]
    
    # Availability windows (in minutes from 9:00 AM)
    # For each friend: [low, high] for start time
    avail_low = [0, 60, 690, 19, 135]   # index0 unused for real meetings
    avail_high = [0, 555, 705, 405, 240] # index0 unused for real meetings
    
    # Create Z3 variables
    s = [Int(f's_{i}') for i in range(5)]
    meet = [Bool(f'meet_{i}') for i in range(5)]
    
    solver = Solver()
    
    # Virtual meeting at Bayview at time 0 (9:00 AM)
    solver.add(meet[0] == True)
    solver.add(s[0] == 0)
    
    # Constraints for real meetings (indices 1 to 4)
    for i in range(1, 5):
        solver.add(Implies(meet[i], And(s[i] >= avail_low[i], s[i] <= avail_high[i])))
    
    # Constraints for every pair of meetings (including virtual)
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            c1 = (s[j] >= s[i] + dur[i] + travel_time[i][j])
            c2 = (s[i] >= s[j] + dur[j] + travel_time[j][i])
            solver.add(Implies(And(meet[i], meet[j]), Or(c1, c2)))
    
    # Objective: maximize the number of meetings (for indices 1 to 4)
    objective = Sum([If(meet[i], 1, 0) for i in range(1,5)])
    
    opt = Optimize()
    opt.add(solver.assertions())
    opt.maximize(objective)
    
    schedule = []
    if opt.check() == sat:
        m = opt.model()
        friends = [None, "Mary", "Lisa", "Betty", "Charles"]
        for i in range(1,5):
            if is_true(m.evaluate(meet[i])):
                start_val = m.evaluate(s[i])
                start_minutes = start_val.as_long()
                total_minutes = start_minutes
                hours = total_minutes // 60
                minutes = total_minutes % 60
                start_time = f"{9+hours:02d}:{minutes:02d}"
                
                end_minutes = start_minutes + dur[i]
                hours_end = end_minutes // 60
                minutes_end = end_minutes % 60
                end_time = f"{9+hours_end:02d}:{minutes_end:02d}"
                
                schedule.append({
                    "action": "meet",
                    "person": friends[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start_time
        schedule.sort(key=lambda x: x['start_time'])
    else:
        # If no solution found, schedule remains empty
        pass
        
    result = {"itinerary": schedule}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()