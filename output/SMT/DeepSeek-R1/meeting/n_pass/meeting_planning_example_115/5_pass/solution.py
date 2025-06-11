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

    # Define solvers and variables for each scenario
    solvers = []
    scenarios = ['both', 'carol', 'jessica']
    
    for scenario in scenarios:
        s = Solver()
        # Common variables
        leave_R = Int(f'leave_R_{scenario}')
        s.add(leave_R >= start_R_min)
        
        if scenario == 'both':
            d_c = Int(f'd_c_{scenario}')
            start_carol = Int(f'start_carol_{scenario}')
            leave_M = Int(f'leave_M_{scenario}')
            arrive_P = Int(f'arrive_P_{scenario}')
            start_jessica = Int(f'start_jessica_{scenario}')
            d_j = Int(f'd_j_{scenario}')
            
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
            d_c = Int(f'd_c_{scenario}')
            start_carol = Int(f'start_carol_{scenario}')
            
            # Constraints for Carol
            s.add(start_carol >= carol_available_start)
            s.add(start_carol + d_c <= carol_available_end)
            s.add(d_c >= 60)
            s.add(leave_R + R_to_M <= start_carol)
            s.add(start_carol >= leave_R + R_to_M)
            
        elif scenario == 'jessica':
            start_jessica = Int(f'start_jessica_{scenario}')
            d_j = Int(f'd_j_{scenario}')
            
            # Constraints for Jessica
            s.add(start_jessica >= jessica_available_start)
            s.add(start_jessica + d_j <= jessica_available_end)
            s.add(d_j >= 45)
            s.add(leave_R + R_to_P <= start_jessica)
            s.add(start_jessica >= leave_R + R_to_P)
        
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
            leave_R_var = Int(f'leave_R_{result}')
            d_c_var = Int(f'd_c_{result}')
            start_carol_var = Int(f'start_carol_{result}')
            leave_M_var = Int(f'leave_M_{result}')
            arrive_P_var = Int(f'arrive_P_{result}')
            start_jessica_var = Int(f'start_jessica_{result}')
            d_j_var = Int(f'd_j_{result}')
            
            leave_R_val = model[leave_R_var].as_long()
            d_c_val = model[d_c_var].as_long()
            start_carol_val = model[start_carol_var].as_long()
            leave_M_val = model[leave_M_var].as_long()
            arrive_P_val = model[arrive_P_var].as_long()
            start_jessica_val = model[start_jessica_var].as_long()
            d_j_val = model[d_j_var].as_long()
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Marina District at: {minutes_to_time(leave_R_val + R_to_M)} (travel time: {R_to_M} minutes)")
            print(f"  Meet Carol from {minutes_to_time(start_carol_val)} to {minutes_to_time(start_carol_val + d_c_val)} ({d_c_val} minutes)")
            print(f"  Leave Marina District at: {minutes_to_time(leave_M_val)}")
            print(f"  Arrive Pacific Heights at: {minutes_to_time(leave_M_val + M_to_P)} (travel time: {M_to_P} minutes)")
            if arrive_P_val < jessica_available_start:
                print(f"  Wait at Pacific Heights from {minutes_to_time(arrive_P_val)} to {minutes_to_time(jessica_available_start)}")
            print(f"  Meet Jessica from {minutes_to_time(start_jessica_val)} to {minutes_to_time(start_jessica_val + d_j_val)} ({d_j_val} minutes)")
        
        elif result == 'carol':
            leave_R_var = Int(f'leave_R_{result}')
            d_c_var = Int(f'd_c_{result}')
            start_carol_var = Int(f'start_carol_{result}')
            
            leave_R_val = model[leave_R_var].as_long()
            d_c_val = model[d_c_var].as_long()
            start_carol_val = model[start_carol_var].as_long()
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Marina District at: {minutes_to_time(leave_R_val + R_to_M)} (travel time: {R_to_M} minutes)")
            print(f"  Meet Carol from {minutes_to_time(start_carol_val)} to {minutes_to_time(start_carol_val + d_c_val)} ({d_c_val} minutes)")
            print("  No meeting with Jessica.")
        
        elif result == 'jessica':
            leave_R_var = Int(f'leave_R_{result}')
            start_jessica_var = Int(f'start_jessica_{result}')
            d_j_var = Int(f'd_j_{result}')
            
            leave_R_val = model[leave_R_var].as_long()
            start_jessica_val = model[start_jessica_var].as_long()
            d_j_val = model[d_j_var].as_long()
            
            print(f"  Leave Richmond District at: {minutes_to_time(leave_R_val)}")
            print(f"  Arrive Pacific Heights at: {minutes_to_time(leave_R_val + R_to_P)} (travel time: {R_to_P} minutes)")
            print(f"  Meet Jessica from {minutes_to_time(start_jessica_val)} to {minutes_to_time(start_jessica_val + d_j_val)} ({d_j_val} minutes)")
            print("  No meeting with Carol.")

if __name__ == '__main__':
    main()