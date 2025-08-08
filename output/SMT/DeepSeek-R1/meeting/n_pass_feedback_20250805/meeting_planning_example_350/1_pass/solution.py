from z3 import *
import json

def main():
    # Travel times from Bayview to each meeting location (in minutes)
    T0 = [23, 13, 19, 19]  # [Mary, Lisa, Betty, Charles]
    
    # Travel time matrix between meetings: T[i][j] = time from meeting i to meeting j
    T = [
        [0, 15, 11, 13],  # Mary to [Mary, Lisa, Betty, Charles]
        [16, 0, 12, 17],  # Lisa to [Mary, Lisa, Betty, Charles]
        [12, 11, 0, 21],  # Betty to [Mary, Lisa, Betty, Charles]
        [13, 17, 19, 0]   # Charles to [Mary, Lisa, Betty, Charles]
    ]
    
    # Meeting durations (in minutes)
    durations = [45, 75, 90, 120]  # Mary, Lisa, Betty, Charles
    
    # Availability windows for start times (in minutes from 9:00 AM)
    # [start_min, end_min] where end_min = available_end - duration
    availability = [
        (60, 555),   # Mary: 10:00 AM to 7:00 PM -> start by 6:15 PM (555 minutes)
        (690, 705),  # Lisa: 8:30 PM to 10:00 PM -> start by 8:45 PM (705 minutes)
        (0, 405),    # Betty: 9:00 AM to 5:15 PM -> start by 3:45 PM (405 minutes)
        (135, 240)   # Charles: 11:15 AM to 3:00 PM -> start by 1:00 PM (240 minutes)
    ]
    
    # Initialize Z3 solver and variables
    opt = Optimize()
    s0, s1, s2, s3 = Bools('s0 s1 s2 s3')
    scheduled = [s0, s1, s2, s3]
    m0, m1, m2, m3 = Ints('m0 m1 m2 m3')
    start_times = [m0, m1, m2, m3]
    names = ["Mary", "Lisa", "Betty", "Charles"]
    
    # Add constraints for each meeting
    for i in range(4):
        low, high = availability[i]
        opt.add(Implies(scheduled[i], And(start_times[i] >= T0[i], start_times[i] >= low, start_times[i] <= high)))
    
    # Add disjunctive constraints for pairs of meetings
    for i in range(4):
        for j in range(i+1, 4):
            b_ij = Bool(f'b_{i}_{j}')
            opt.add(Implies(And(scheduled[i], scheduled[j]), 
                           Or(And(b_ij, start_times[j] >= start_times[i] + durations[i] + T[i][j]),
                              And(Not(b_ij), start_times[i] >= start_times[j] + durations[j] + T[j][i])
                           )))
    
    # Maximize the number of scheduled meetings
    cost = Sum([If(s, 1, 0) for s in scheduled])
    opt.maximize(cost)
    
    # Solve and process the model
    itinerary = []
    if opt.check() == sat:
        model = opt.model()
        for i in range(4):
            if model.evaluate(scheduled[i]):
                start_val = model.evaluate(start_times[i]).as_long()
                hours = 9 + start_val // 60
                minutes = start_val % 60
                start_time = f"{hours:02d}:{minutes:02d}"
                end_val = start_val + durations[i]
                end_hours = 9 + end_val // 60
                end_minutes = end_val % 60
                end_time = f"{end_hours:02d}:{end_minutes:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
    
    # Output the solution
    print("SOLUTION:")
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()