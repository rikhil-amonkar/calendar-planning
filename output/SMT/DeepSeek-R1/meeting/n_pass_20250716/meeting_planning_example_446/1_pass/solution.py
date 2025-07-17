from z3 import *

def main():
    # Travel times matrix: 0=Richmond, 1=Marina, 2=Chinatown, 3=Financial, 4=Bayview, 5=Union Square
    travel = [
        [0, 9, 20, 22, 26, 21],
        [11, 0, 16, 17, 27, 16],
        [20, 12, 0, 5, 22, 7],
        [21, 15, 5, 0, 19, 9],
        [25, 25, 18, 19, 0, 17],
        [20, 18, 7, 9, 15, 0]
    ]
    
    # Available start and end times in minutes from 9:00 AM (0 minutes)
    # For real meetings: [Kimberly, Robert, Rebecca, Margaret, Kenneth]
    available_start = [255, 195, 255, 30, 630]  # 1:15PM, 12:15PM, 1:15PM, 9:30AM, 7:30PM
    available_end = [465, 675, 465, 270, 735]   # 4:45PM, 8:15PM, 4:45PM, 1:30PM, 9:15PM
    min_durations = [15, 15, 75, 30, 75]        # in minutes

    # Solver
    opt = Optimize()
    
    # Variables for the 5 real meetings
    meet = [Bool(f'meet{i}') for i in range(5)]
    start = [Int(f'start{i}') for i in range(5)]
    
    # Active flags for 6 meetings: dummy (always active) and 5 real meetings
    active = [True] + [meet[i] for i in range(5)]
    # Start times for 6 meetings: dummy at 0, then real meetings
    start_times = [0] + [start[i] for i in range(5)]
    # Durations for 6 meetings: dummy 0, then real meetings
    durations = [0] + min_durations
    # District indices for 6 meetings: dummy=0 (Richmond), then 1 to 5 for real meetings
    districts = [0, 1, 2, 3, 4, 5]
    
    # Constraint 1: For each real meeting, if active, must be within availability window
    for i in range(5):
        opt.add(Implies(meet[i], And(start[i] >= available_start[i], 
                                    start[i] + min_durations[i] <= available_end[i])))
    
    # Constraint 2: For every pair of meetings (i,j) with i < j, if both active, enforce travel time
    for i in range(6):
        for j in range(i+1, 6):
            if i == j:
                continue
            # Condition: if both meetings are active
            condition = And(active[i], active[j])
            # Option 1: i before j
            option1 = (start_times[i] + durations[i] + travel[districts[i]][districts[j]] <= start_times[j])
            # Option 2: j before i
            option2 = (start_times[j] + durations[j] + travel[districts[j]][districts[i]] <= start_times[i])
            # Add constraint: if both active, then either option1 or option2
            opt.add(Implies(condition, Or(option1, option2)))
    
    # Maximize the number of friends met
    total_met = Sum([If(meet[i], 1, 0) for i in range(5)])
    opt.maximize(total_met)
    
    # Solve
    if opt.check() == sat:
        m = opt.model()
        total_met_val = m.evaluate(total_met)
        print(f"Total friends met: {total_met_val}")
        
        # Print schedule for each friend if met
        friends = ['Kimberly (Marina)', 'Robert (Chinatown)', 'Rebecca (Financial)', 'Margaret (Bayview)', 'Kenneth (Union Square)']
        for i in range(5):
            if m.evaluate(meet[i]):
                s = m.evaluate(start[i])
                start_minutes = s.as_long()
                hours = start_minutes // 60
                minutes = start_minutes % 60
                start_time_str = f"{9 + hours}:{minutes:02d} {'AM' if hours < 3 else 'PM'}" 
                end_time = start_minutes + min_durations[i]
                end_hours = end_time // 60
                end_minutes = end_time % 60
                end_time_str = f"{9 + end_hours}:{end_minutes:02d} {'AM' if end_hours < 3 else 'PM'}"
                print(f"Meet {friends[i]} from {start_time_str} to {end_time_str}")
            else:
                print(f"Did not meet {friends[i]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()