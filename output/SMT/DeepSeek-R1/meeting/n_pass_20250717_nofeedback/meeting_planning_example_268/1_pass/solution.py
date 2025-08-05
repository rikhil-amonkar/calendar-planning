from z3 import *

def min_to_time(minutes):
    total_min = minutes
    hours = total_min // 60
    mins = total_min % 60
    hour_24 = 9 + hours
    return "{:02d}:{:02d}".format(hour_24, mins)

def solve_sequence1():
    T_start = Int('T_start_seq1')
    J_start = Int('J_start_seq1')
    M_start = Int('M_start_seq1')
    
    T_duration = 105
    J_duration = 60
    M_duration = 60
    
    T_end = T_start + T_duration
    J_end = J_start + J_duration
    M_end = M_start + M_duration
    
    s = Solver()
    
    # Constraints for Timothy at AS
    s.add(T_start >= 180)  # 12:00 PM
    s.add(T_end <= 435)    # 4:15 PM
    
    # Travel from GGP to AS: 10 minutes (arrive at T_start)
    # We start at GGP at time 0, so T_start >= 10 (but 180>10, so redundant)
    
    # Travel from AS to RH: 13 minutes after Timothy meeting
    arrive_RH = T_end + 13
    s.add(J_start >= arrive_RH)
    s.add(J_start >= 465)  # 4:45 PM
    s.add(J_end <= 750)    # 9:30 PM
    
    # Travel from RH to P: 14 minutes after Joseph meeting
    arrive_P = J_end + 14
    s.add(M_start >= arrive_P)
    s.add(M_start >= 585)  # 6:45 PM
    s.add(M_end <= 720)    # 9:00 PM
    
    if s.check() == sat:
        m = s.model()
        t_start_val = m.eval(T_start).as_long()
        j_start_val = m.eval(J_start).as_long()
        m_start_val = m.eval(M_start).as_long()
        
        t_end_val = t_start_val + T_duration
        j_end_val = j_start_val + J_duration
        m_end_val = m_start_val + M_duration
        
        return [
            {"action": "meet", "person": "Timothy", "start_time": min_to_time(t_start_val), "end_time": min_to_time(t_end_val)},
            {"action": "meet", "person": "Joseph", "start_time": min_to_time(j_start_val), "end_time": min_to_time(j_end_val)},
            {"action": "meet", "person": "Mark", "start_time": min_to_time(m_start_val), "end_time": min_to_time(m_end_val)}
        ]
    else:
        return None

def solve_sequence2():
    T_start = Int('T_start_seq2')
    M_start = Int('M_start_seq2')
    J_start = Int('J_start_seq2')
    
    T_duration = 105
    M_duration = 60
    J_duration = 60
    
    T_end = T_start + T_duration
    M_end = M_start + M_duration
    J_end = J_start + J_duration
    
    s = Solver()
    
    # Constraints for Timothy at AS
    s.add(T_start >= 180)  # 12:00 PM
    s.add(T_end <= 435)    # 4:15 PM
    
    # Travel from AS to P: 18 minutes
    arrive_P = T_end + 18
    s.add(M_start >= arrive_P)
    s.add(M_start >= 585)  # 6:45 PM
    s.add(M_end <= 720)    # 9:00 PM
    
    # Travel from P to RH: 14 minutes
    arrive_RH = M_end + 14
    s.add(J_start >= arrive_RH)
    s.add(J_start >= 465)  # 4:45 PM
    s.add(J_end <= 750)    # 9:30 PM
    
    if s.check() == sat:
        m = s.model()
        t_start_val = m.eval(T_start).as_long()
        m_start_val = m.eval(M_start).as_long()
        j_start_val = m.eval(J_start).as_long()
        
        t_end_val = t_start_val + T_duration
        m_end_val = m_start_val + M_duration
        j_end_val = j_start_val + J_duration
        
        return [
            {"action": "meet", "person": "Timothy", "start_time": min_to_time(t_start_val), "end_time": min_to_time(t_end_val)},
            {"action": "meet", "person": "Mark", "start_time": min_to_time(m_start_val), "end_time": min_to_time(m_end_val)},
            {"action": "meet", "person": "Joseph", "start_time": min_to_time(j_start_val), "end_time": min_to_time(j_end_val)}
        ]
    else:
        return None

def main():
    itinerary_seq1 = solve_sequence1()
    if itinerary_seq1 is not None:
        result = {"itinerary": itinerary_seq1}
        print('SOLUTION:')
        print(result)
        return
    
    itinerary_seq2 = solve_sequence2()
    if itinerary_seq2 is not None:
        result = {"itinerary": itinerary_seq2}
        print('SOLUTION:')
        print(result)
        return
    
    # If both sequences fail, try meeting only two friends (not required as both sequences work)
    print('SOLUTION:')
    print({"itinerary": []})

if __name__ == "__main__":
    main()