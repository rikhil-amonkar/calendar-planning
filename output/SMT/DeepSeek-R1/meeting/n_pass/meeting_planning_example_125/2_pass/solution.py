from z3 import *

def format_time(minutes_from_9am):
    total_minutes = 540 + minutes_from_9am  # 540 minutes = 9:00 AM
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    s = Solver()
    
    s_start = Int('s_start')
    j_start = Int('j_start')
    
    s_end = s_start + 90
    j_end = j_start + 30
    
    s.add(s_start >= 5)  # Arrive at Financial District by 9:05 AM
    s.add(s_end <= 150)  # Stephanie must end by 11:30 AM (150 minutes from 9:00 AM)
    
    s.add(j_start >= 75)  # John available from 10:15 AM (75 minutes from 9:00 AM)
    s.add(j_end <= 705)   # John must end by 8:45 PM (705 minutes from 9:00 AM)
    
    order1 = And(
        s_start >= 5,
        j_start >= s_end + 17  # Travel from Financial District to Alamo Square
    )
    order2 = And(
        j_start >= 19,  # Travel from Embarcadero to Alamo Square
        s_start >= j_end + 17  # Travel from Alamo Square to Financial District
    )
    s.add(Or(order1, order2))
    
    if s.check() == sat:
        m = s.model()
        s_start_val = m.eval(s_start).as_long()
        s_end_val = s_start_val + 90
        j_start_val = m.eval(j_start).as_long()
        j_end_val = j_start_val + 30
        
        steph_meeting = {
            "action": "meet",
            "person": "Stephanie",
            "start_time": format_time(s_start_val),
            "end_time": format_time(s_end_val)
        }
        john_meeting = {
            "action": "meet",
            "person": "John",
            "start_time": format_time(j_start_val),
            "end_time": format_time(j_end_val)
        }
        
        itinerary = [steph_meeting, john_meeting]
        itinerary.sort(key=lambda x: x["start_time"])
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No feasible schedule found")

if __name__ == "__main__":
    main()