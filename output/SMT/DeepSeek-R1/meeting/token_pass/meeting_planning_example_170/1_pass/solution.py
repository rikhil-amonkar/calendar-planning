from z3 import *
import json

def main():
    # Convert all times to minutes since midnight
    start_time_nb = 9 * 60  # 9:00 AM
    emily_available_start = 16 * 60  # 16:00
    emily_available_end = 17 * 60 + 15  # 17:15
    margaret_available_start = 19 * 60  # 19:00
    margaret_available_end = 21 * 60  # 21:00
    
    min_emily_duration = 45
    min_margaret_duration = 120
    
    travel_times = {
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11
    }
    
    s = Solver()
    
    # Meeting time variables
    e_start = Int('e_start')
    e_end = Int('e_end')
    m_start = Int('m_start')
    m_end = Int('m_end')
    
    # Meeting duration constraints
    s.add(e_end - e_start >= min_emily_duration)
    s.add(m_end - m_start >= min_margaret_duration)
    
    # Availability constraints
    s.add(e_start >= emily_available_start)
    s.add(e_end <= emily_available_end)
    s.add(m_start >= margaret_available_start)
    s.add(m_end <= margaret_available_end)
    
    # Travel constraints for both possible orders
    order1 = And(
        e_start >= start_time_nb + travel_times[("North Beach", "Union Square")],
        m_start >= e_end + travel_times[("Union Square", "Russian Hill")]
    )
    
    order2 = And(
        m_start >= start_time_nb + travel_times[("North Beach", "Russian Hill")],
        e_start >= m_end + travel_times[("Russian Hill", "Union Square")]
    )
    
    s.add(Or(order1, order2))
    
    if s.check() == sat:
        model = s.model()
        e_start_val = model[e_start].as_long()
        e_end_val = model[e_end].as_long()
        m_start_val = model[m_start].as_long()
        m_end_val = model[m_end].as_long()
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        itinerary = [
            {
                "action": "meet",
                "location": "Union Square",
                "person": "Emily",
                "start_time": format_time(e_start_val),
                "end_time": format_time(e_end_val)
            },
            {
                "action": "meet",
                "location": "Russian Hill",
                "person": "Margaret",
                "start_time": format_time(m_start_val),
                "end_time": format_time(m_end_val)
            }
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()