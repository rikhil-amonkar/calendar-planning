from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes
    R_to_M = 9
    R_to_P = 10
    M_to_P = 7
    M_to_R = 11
    P_to_M = 6
    P_to_R = 12

    # Convert time to minutes
    start_R_min = 9 * 60  # 9:00 AM
    carol_available_start = 11 * 60 + 30  # 11:30 AM
    carol_available_end = 15 * 60  # 3:00 PM
    jessica_available_start = 15 * 60 + 30  # 3:30 PM
    jessica_available_end = 16 * 60 + 45  # 4:45 PM

    # Define solvers for each scenario
    solvers = []
    scenarios = ['both', 'carol', 'jessica']
    
    for scenario in scenarios:
        s = Solver()
        # Common variables
        leave_R = Int('leave_R_' + scenario)
        d_c = Int('d_c_' + scenario)
        start_carol = Int('start_carol_' + scenario)
        leave_M = Int('leave_M_' + scenario)
        arrive_P = Int('arrive_P_' + scenario)
        start_jessica = Int('start_jessica_' + scenario)
        d_j = Int('d_j_' + scenario)
        
        # Common constraints for leaving Richmond
        s.add(leave_R >= start_R_min)
        
        if scenario == 'both' or scenario == 'carol':
            # Constraints for meeting Carol
            s.add(start_carol >= carol_available_start)
            s.add(start_carol + d_c <= carol_available_end)
            s.add(d_c >= 60)
            s.add(leave_R + R_to_M <= start_carol)  # Arrive at M by start_carol
            s.add(start_carol >= leave_R + R_to_M)   # Arrival time at M
            
            if scenario == 'both':
                # Constraints for traveling to Jessica
                s.add(leave_M == start_carol + d_c)
                s.add(arrive_P == leave_M + M_to_P)
                # Constraints for meeting Jessica
                s.add(start_jessica >= jessica_available_start)
                s.add(start_jessica >= arrive_P)  # Cannot start before arrival
                s.add(start_jessica + d_j <= jessica_available_end)
                s.add(d_j >= 45)
        
        if scenario == 'jessica':
            # Constraints for meeting Jessica
            s.add(start_jessica >= jessica_available_start)
            s.add(start_jessica + d_j <= jessica_available_end)
            s.add(d_j >= 45)
            s.add(leave_R + R_to_P <= start_jessica)  # Arrive at P by start_jessica
            s.add(start_jessica >= leave_R + R_to_P)   # Arrival time at P
        
        solvers.append((scenario, s))
    
    # Check scenarios in priority order
    result = None
    model = None
    for scenario, s in solvers:
        if s.check() == sat:
            model = s.model()
            result = scenario
            break
    
    # Output the result
    if result is None:
        print("SOLUTION: Unable to meet any friends.")
    else:
        print("SOLUTION: We can meet " + 
              ("both friends." if result == 'both' else 
               "Carol." if result == 'carol' else "Jessica."))
        print("Detailed schedule:")
        if result == 'both':
            leave_R_val = int(str(model.eval(leave_R)))
            d_c_val = int(str(model.eval(d_c)))
            start_carol_val = int(str(model.eval(start_carol)))
            leave_M_val = int(str(model.eval(leave_M)))
            arrive_P_val = int(str(model.eval(arrive_P)))
            start_jessica_val = int(str(model.eval(start_jessica)))
            d_j_val = int(str(model.eval(d_j)))
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Marina District at: {minutes_to_time(leave_R_val + R_to_M)} (travel time: {R_to_M} minutes)")
            print(f"  Meet Carol from {minutes_to_time(start_carol_val)} to {minutes_to_time(start_carol_val + d_c_val)} ({d_c_val} minutes)")
            print(f"  Leave Marina District at: {minutes_to_time(leave_M_val)}")
            print(f"  Arrive Pacific Heights at: {minutes_to_time(leave_M_val + M_to_P)} (travel time: {M_to_P} minutes)")
            if arrive_P_val < jessica_available_start:
                print(f"  Wait at Pacific Heights from {minutes_to_time(arrive_P_val)} to {minutes_to_time(jessica_available_start)}")
            print(f"  Meet Jessica from {minutes_to_time(start_jessica_val)} to {minutes_to_time(start_jessica_val + d_j_val)} ({d_j_val} minutes)")
        
        elif result == 'carol':
            leave_R_val = int(str(model.eval(leave_R)))
            d_c_val = int(str(model.eval(d_c)))
            start_carol_val = int(str(model.eval(start_carol)))
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Marina District at: {minutes_to_time(leave_R_val + R_to_M)} (travel time: {R_to_M} minutes)")
            print(f"  Meet Carol from {minutes_to_time(start_carol_val)} to {minutes_to_time(start_carol_val + d_c_val)} ({d_c_val} minutes)")
            print("  No meeting with Jessica.")
        
        elif result == 'jessica':
            leave_R_val = int(str(model.eval(leave_R)))
            d_j_val = int(str(model.eval(d_j)))
            start_jessica_val = int(str(model.eval(start_jessica)))
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Pacific Heights at: {minutes_to_time(leave_R_val + R_to_P)} (travel time: {R_to_P} minutes)")
            print(f"  Meet Jessica from {minutes_to_time(start_jessica_val)} to {minutes_to_time(start_jessica_val + d_j_val)} ({d_j_val} minutes)")
            print("  No meeting with Carol.")

if __name__ == '__main__':
    main()