from z3 import *
import json

def format_time(minutes):
    hours = minutes // 60
    minutes_part = minutes % 60
    return f"{hours:02d}:{minutes_part:02d}"

def main():
    # Try Order0: Daniel -> Margaret -> Charles -> Stephanie
    s0 = Solver()
    
    # Times in minutes
    # Daniel: available [480, 810] (8:00 AM to 1:30 PM), min_dur=15
    # Margaret: available [540, 960] (9:00 AM to 4:00 PM), min_dur=30
    # Charles: available [1080, 1245] (6:00 PM to 8:45 PM), min_dur=90
    # Stephanie: available [1230, 1320] (8:30 PM to 10:00 PM), min_dur=90

    # Define variables for start times
    d_start = Int('d_start')
    m_start = Int('m_start')
    c_start = Int('c_start')
    s_start = Int('s_start')
    
    # Fixed durations (minimum)
    d_dur = 15
    m_dur = 30
    c_dur = 90
    s_dur = 90
    
    # End times
    d_end = d_start + d_dur
    m_end = m_start + m_dur
    c_end = c_start + c_dur
    s_end = s_start + s_dur
    
    # Constraints for Order0
    # Start at Sunset at 540 (9:00 AM)
    # Travel to Daniel (Golden Gate Park): 11 minutes
    s0.add(d_start >= 540 + 11)
    s0.add(d_end <= 810)   # Daniel available until 1:30 PM (810 minutes)
    
    # Travel from Daniel to Margaret (Russian Hill): 19 minutes
    s0.add(m_start >= d_end + 19)
    s0.add(m_end <= 960)   # Margaret available until 4:00 PM (960 minutes)
    
    # Travel from Margaret to Charles (Alamo Square): 15 minutes
    arrival_c = m_end + 15
    s0.add(c_start == If(arrival_c >= 1080, arrival_c, 1080))
    s0.add(c_end <= 1245)   # Charles available until 8:45 PM (1245 minutes)
    
    # Travel from Charles to Stephanie (Mission District): 10 minutes
    arrival_s = c_end + 10
    s0.add(s_start == If(arrival_s >= 1230, arrival_s, 1230))
    s0.add(s_end <= 1320)   # Stephanie available until 10:00 PM (1320 minutes)
    
    itinerary = []
    if s0.check() == sat:
        m = s0.model()
        d_start_val = m[d_start].as_long()
        m_start_val = m[m_start].as_long()
        c_start_val = m[c_start].as_long()
        s_start_val = m[s_start].as_long()
        
        itinerary = [
            {"action": "meet", "person": "Daniel", "start_time": format_time(d_start_val), "end_time": format_time(d_start_val + d_dur)},
            {"action": "meet", "person": "Margaret", "start_time": format_time(m_start_val), "end_time": format_time(m_start_val + m_dur)},
            {"action": "meet", "person": "Charles", "start_time": format_time(c_start_val), "end_time": format_time(c_start_val + c_dur)},
            {"action": "meet", "person": "Stephanie", "start_time": format_time(s_start_val), "end_time": format_time(s_start_val + s_dur)}
        ]
    else:
        # Try Order1: Margaret -> Daniel -> Charles -> Stephanie
        s1 = Solver()
        
        # Redefine variables for Order1
        m_start = Int('m_start')
        d_start = Int('d_start')
        c_start = Int('c_start')
        s_start = Int('s_start')
        
        # End times
        m_end = m_start + m_dur
        d_end = d_start + d_dur
        c_end = c_start + c_dur
        s_end = s_start + s_dur
        
        # Constraints for Order1
        # Start at Sunset at 540
        # Travel to Margaret (Russian Hill): 24 minutes
        s1.add(m_start >= 540 + 24)
        s1.add(m_end <= 960)
        
        # Travel from Margaret to Daniel (Golden Gate Park): 21 minutes
        s1.add(d_start >= m_end + 21)
        s1.add(d_end <= 810)   # Daniel available until 1:30 PM (810)
        
        # Travel from Daniel to Charles (Alamo Square): 10 minutes
        arrival_c = d_end + 10
        s1.add(c_start == If(arrival_c >= 1080, arrival_c, 1080))
        s1.add(c_end <= 1245)
        
        # Travel from Charles to Stephanie (Mission District): 10 minutes
        arrival_s = c_end + 10
        s1.add(s_start == If(arrival_s >= 1230, arrival_s, 1230))
        s1.add(s_end <= 1320)
        
        if s1.check() == sat:
            m = s1.model()
            m_start_val = m[m_start].as_long()
            d_start_val = m[d_start].as_long()
            c_start_val = m[c_start].as_long()
            s_start_val = m[s_start].as_long()
            
            itinerary = [
                {"action": "meet", "person": "Margaret", "start_time": format_time(m_start_val), "end_time": format_time(m_start_val + m_dur)},
                {"action": "meet", "person": "Daniel", "start_time": format_time(d_start_val), "end_time": format_time(d_start_val + d_dur)},
                {"action": "meet", "person": "Charles", "start_time": format_time(c_start_val), "end_time": format_time(c_start_val + c_dur)},
                {"action": "meet", "person": "Stephanie", "start_time": format_time(s_start_val), "end_time": format_time(s_start_val + s_dur)}
            ]
        else:
            # Handle fewer meetings if needed (not required as both orders work)
            itinerary = []
    
    # Output the solution
    print("SOLUTION:")
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()