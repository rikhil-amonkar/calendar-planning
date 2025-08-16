from z3 import *
import json

def to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def main():
    # We use minutes from midnight.
    # 9:00 AM = 540, 8:15 AM = 495, 13:30 = 810, 13:15 = 795, 14:30 = 870, 19:30 = 1170, 21:15 = 1275
    
    # Create an Optimize object so we can “optimize” waiting time between meetings.
    opt = Optimize()
    
    # Define meeting time variables (in minutes)
    # Melissa is met at North Beach; available [8:15, 13:30] but we leave Sunset (9:00) and must travel.
    M_start = Int('M_start')  # start time of meeting Melissa at North Beach
    M_end   = Int('M_end')    # end time of meeting Melissa
    
    # Anthony is met at Chinatown; available [13:15, 14:30]
    A_start = Int('A_start')  # start time of meeting Anthony at Chinatown
    A_end   = Int('A_end')    # end time of meeting Anthony
    
    # Rebecca is met at Russian Hill; available [19:30, 21:15].
    # Because the available window exactly equals the minimum required 105 minutes,
    # we fix Rebecca’s meeting to that interval.
    R_start = 1170  # 19:30 in minutes
    R_end   = 1275  # 21:15 in minutes
    
    # Travel times between locations (in minutes):
    # From Sunset District (starting point at 9:00 AM, 540 minutes) to North Beach: 29 minutes.
    # From North Beach to Chinatown: 6 minutes.
    # From Chinatown to Russian Hill: 7 minutes.
    
    # Constraint: You start at Sunset at 9:00.
    # So you cannot start meeting Melissa at North Beach until you travel for 29 minutes:
    opt.add(M_start >= 540 + 29)  # M_start >= 569

    # Melissa is available at North Beach from 8:15 until 13:30.
    # (Though realistically you can only meet her after you arrive, so the lower bound is 569.)
    opt.add(M_end <= 810)
    
    # You need to meet Melissa for at least 105 minutes.
    opt.add(M_end - M_start >= 105)
    
    # Anthony is available in Chinatown between 13:15 and 14:30.
    opt.add(A_start >= 795)
    opt.add(A_end <= 870)
    # You need to meet Anthony for at least 60 minutes.
    opt.add(A_end - A_start >= 60)
    
    # After Melissa (at North Beach) you must travel to Chinatown (to meet Anthony),
    # which takes 6 minutes.
    opt.add(A_start >= M_end + 6)
    
    # After finishing with Anthony in Chinatown, you travel to Russian Hill (to meet Rebecca),
    # which takes 7 minutes. Rebecca begins at 19:30 so you need to have left Anthony in time.
    opt.add(R_start >= A_end + 7)
    
    # Optional: Optimize your schedule by minimizing waiting time.
    # Waiting time breaks down as follows:
    #   - Waiting at North Beach from arrival (9:00+29=569) to when you actually start meeting Melissa.
    #   - Waiting after finishing with Melissa until you start meeting Anthony.
    #   - Waiting after finishing with Anthony until Rebecca’s meeting begins.
    waiting_to_melissa = M_start - (540 + 29)           # time after arriving at North Beach
    waiting_at_anthony = A_start - (M_end + 6)             # time gap after Melissa’s meeting while traveling to Chinatown
    waiting_for_rebecca = R_start - (A_end + 7)            # time gap after Anthony’s meeting until Rebecca starts
    total_waiting = waiting_to_melissa + waiting_at_anthony + waiting_for_rebecca
    opt.minimize(total_waiting)
    
    # Check for a solution.
    if opt.check() == sat:
        m = opt.model()
        M_start_val = m[M_start].as_long()
        M_end_val   = m[M_end].as_long()
        A_start_val = m[A_start].as_long()
        A_end_val   = m[A_end].as_long()
        
        itinerary = [
            {"action": "meet", "person": "Melissa",
             "start_time": to_time(M_start_val), "end_time": to_time(M_end_val)},
            {"action": "meet", "person": "Anthony",
             "start_time": to_time(A_start_val), "end_time": to_time(A_end_val)},
            {"action": "meet", "person": "Rebecca",
             "start_time": to_time(R_start), "end_time": to_time(R_end)}
        ]
        
        print(json.dumps({"itinerary": itinerary}, indent=4))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()