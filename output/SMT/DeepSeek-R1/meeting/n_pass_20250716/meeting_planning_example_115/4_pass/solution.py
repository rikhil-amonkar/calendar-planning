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
        s.add(leave_R >= start_R_min)
        
        if scenario == 'both':
            d_c = Int('d_c_both')
            start_carol = Int('start_carol_both')
            leave_M = Int('leave_M_both')
            arrive_P = Int('arrive_P_both')
            start_jessica = Int('start_jessica_both')
            d_j = Int('d_j_both')
            
            # Constraints for Carol
            s.add(start_carol >= carol_available_start)
            s.add(start_carol + d_c <= carol_available_end)
            s.add(d_c >= 60)
            s.add(leave_R + R_to_M <= start_carol)
            s.add(start_carol >= leave_R + R_to_M)
            
            # Constraints for Jessica
            s.add(leave_M == start_carol + d_c)
            s.add(arrive_P == leave_M + M_to_P)
            s.add(start_jessica >= jessica_available_start)
            s.add(start_jessica >= arrive_P)
            s.add(start_jessica + d_j <= jessica_available_end)
            s.add(d_j >= 45)
            
        elif scenario == 'carol':
            d_c = Int('d_c_carol')
            start_carol = Int('start_carol_carol')
            
            # Constraints for Carol
            s.add(start_carol >= carol_available_start)
            s.add(start_carol + d_c <= carol_available_end)
            s.add(d_c >= 60)
            s.add(leave_R + R_to_M <= start_carol)
            s.add(start_carol >= leave_R + R_to_M)
            
        elif scenario == 'jessica':
            start_jessica = Int('start_jessica_jessica')
            d_j = Int('d_j_jessica')
            
            # Constraints for Jessica
            s.add(start_jessica >= jessica_available_start)
            s.add(start_jessica + d_j <= jessica_available_end)
            s.add(d_j >= 45)
            s.add(leave_R + R_to_P <= start_jessica)
        
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
            leave_R_val = model.eval(leave_R).as_long()
            d_c_val = model.eval(d_c).as_long()
            start_carol_val = model.eval(start_carol).as_long()
            leave_M_val = model.eval(leave_M).as_long()
            arrive_P_val = model.eval(arrive_P).as_long()
            start_jessica_val = model.eval(start_jessica).as_long()
            d_j_val = model.eval(d_j).as_long()
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Marina District at: {minutes_to_time(leave_R_val + R_to_M)} (travel time: {R_to_M} minutes)")
            print(f"  Meet Carol from {minutes_to_time(start_carol_val)} to {minutes_to_time(start_carol_val + d_c_val)} ({d_c_val} minutes)")
            print(f"  Leave Marina District at: {minutes_to_time(leave_M_val)}")
            print(f"  Arrive Pacific Heights at: {minutes_to_time(leave_M_val + M_to_P)} (travel time: {M_to_P} minutes)")
            if arrive_P_val < jessica_available_start:
                print(f"  Wait at Pacific Heights from {minutes_to_time(arrive_P_val)} to {minutes_to_time(jessica_available_start)}")
            print(f"  Meet Jessica from {minutes_to_time(start_jessica_val)} to {minutes_to_time(start_jessica_val + d_j_val)} ({d_j_val} minutes)")
        
        elif result == 'carol':
            leave_R_val = model.eval(leave_R).as_long()
            d_c_val = model.eval(d_c).as_long()
            start_carol_val = model.eval(start_carol).as_long()
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Marina District at: {minutes_to_time(leave_R_val + R_to_M)} (travel time: {R_to_M} minutes)")
            print(f"  Meet Carol from {minutes_to_time(start_carol_val)} to {minutes_to_time(start_carol_val + d_c_val)} ({d_c_val} minutes)")
            print("  No meeting with Jessica.")
        
        elif result == 'jessica':
            leave_R_val = model.eval(leave_R).as_long()
            start_jessica_val = model.eval(start_jessica).as_long()
            d_j_val = model.eval(d_j).as_long()
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Pacific Heights at: {minutes_to_time(leave_R_val + R_to_P)} (travel time: {R_to_P} minutes)")
            print(f"  Meet Jessica from {minutes_to_time(start_jessica_val)} to {minutes_to_time(start_jessica_val + d_j_val)} ({d_j_val} minutes)")
            print("  No meeting with Carol.")

if __name__ == '__main__':
    main()