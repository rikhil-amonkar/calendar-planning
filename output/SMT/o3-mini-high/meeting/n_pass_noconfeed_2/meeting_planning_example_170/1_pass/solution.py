import json
from z3 import Optimize, Int, sat

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()
    
    # Define decision variables for Emily's meeting start and end times (in minutes from midnight)
    # 9:00 AM is 540, 16:00 is 960, 17:15 is 1035, 19:00 is 1140, 21:00 is 1260.
    e_start = Int('e_start')
    e_end = Int('e_end')
    
    # Fixed times for Margaret's meeting at Russian Hill.
    m_start = 1140  # 19:00
    m_end = 1260    # 21:00
    
    # Add constraints for Emily's meeting at Union Square.
    # Emily is available from 16:00 (960) to 17:15 (1035) and meeting must be at least 45 minutes.
    opt.add(e_start >= 960)
    opt.add(e_end <= 1035)
    opt.add(e_end - e_start >= 45)
    opt.add(e_start < e_end)
    
    # Travel constraints:
    # You arrive at North Beach at 9:00 AM (540) and must travel to Union Square (7 minutes) for Emily.
    opt.add(540 + 7 <= e_start)
    
    # After meeting Emily at Union Square, travel from Union Square to Russian Hill takes 13 minutes.
    # This travel must be completed before Margaret's meeting starts at 19:00 (1140).
    opt.add(e_end + 13 <= m_start)
    
    # Objective: maximize the meeting duration with Emily (and therefore get the most meeting time overall).
    opt.maximize(e_end - e_start)
    
    if opt.check() == sat:
        model = opt.model()
        emily_start = model[e_start].as_long()
        emily_end = model[e_end].as_long()
        
        itinerary = [
            {
                "action": "meet",
                "location": "Union Square",
                "person": "Emily",
                "start_time": minutes_to_time(emily_start),
                "end_time": minutes_to_time(emily_end)
            },
            {
                "action": "meet",
                "location": "Russian Hill",
                "person": "Margaret",
                "start_time": minutes_to_time(m_start),
                "end_time": minutes_to_time(m_end)
            }
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()