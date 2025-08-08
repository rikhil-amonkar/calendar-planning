from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    minutes_remain = minutes % 60
    return f"{hours:02d}:{minutes_remain:02d}"

def main():
    # Initialize the optimizer
    opt = Optimize()
    
    # Convert times to minutes from midnight
    start_time_nb = 9 * 60  # 9:00 AM
    mark_start_min = 13 * 60  # 1:00 PM
    mark_end_min = 17 * 60 + 45  # 5:45 PM
    karen_start_min = 18 * 60 + 45  # 6:45 PM
    karen_end_min = 20 * 60 + 15  # 8:15 PM
    
    # Travel times in minutes
    travel_nb_to_emb = 6  # North Beach to Embarcadero
    travel_emb_to_ph = 11  # Embarcadero to Pacific Heights
    
    # Meeting duration requirements
    mark_min_duration = 120
    karen_min_duration = 90
    
    # Variables for Mark's meeting start and end times (in minutes)
    m_start = Int('m_start')
    m_end = Int('m_end')
    
    # Constraints for Mark
    opt.add(m_start >= mark_start_min)
    opt.add(m_end <= mark_end_min)
    opt.add(m_end - m_start >= mark_min_duration)
    
    # Constraint: Leave North Beach at m_start - travel_nb_to_emb must be after 9:00 AM
    opt.add(m_start - travel_nb_to_emb >= start_time_nb)
    
    # Karen's meeting is fixed to her availability window
    k_start = karen_start_min
    k_end = karen_end_min
    
    # Travel constraint: After meeting Mark, travel to Karen takes 11 minutes
    opt.add(k_start >= m_end + travel_emb_to_ph)
    
    # Objective: Maximize Mark's start time to minimize waiting at Pacific Heights
    opt.maximize(m_start)
    
    # Solve the constraints
    if opt.check() == sat:
        model = opt.model()
        m_s = model[m_start].as_long()
        m_e = model[m_end].as_long()
        
        # Convert to time strings
        mark_start = min_to_time(m_s)
        mark_end = min_to_time(m_e)
        karen_start = min_to_time(k_start)
        karen_end = min_to_time(k_end)
        
        itinerary = [
            {"action": "meet", "person": "Mark", "start_time": mark_start, "end_time": mark_end},
            {"action": "meet", "person": "Karen", "start_time": karen_start, "end_time": karen_end}
        ]
        
        # Output as JSON-formatted dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()