from z3 import *
import json

def main():
    T0 = Int('T0')
    s_j = Int('s_j')
    s_r = Int('s_r')
    order = Bool('order')
    
    opt = Optimize()
    
    opt.add(s_j >= 225, s_j <= 300 - 75)
    opt.add(s_r >= 225, s_r <= 375 - 30)
    opt.add(T0 >= 0)
    
    opt.add(If(order,
              And(s_j >= T0 + 18, s_r >= s_j + 82),
              And(s_r >= T0 + 22, s_j >= s_r + 37)
            ))
    
    opt.minimize(s_r)
    
    if opt.check() == sat:
        m = opt.model()
        s_j_val = m[s_j].as_long()
        s_r_val = m[s_r].as_long()
        
        def min_to_time(minutes):
            total_minutes = minutes
            h = 9 + total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"
        
        meeting_james = {
            "action": "meet",
            "person": "James",
            "start_time": min_to_time(s_j_val),
            "end_time": min_to_time(s_j_val + 75)
        }
        
        meeting_robert = {
            "action": "meet",
            "person": "Robert",
            "start_time": min_to_time(s_r_val),
            "end_time": min_to_time(s_r_val + 30)
        }
        
        itinerary_list = [meeting_james, meeting_robert]
        itinerary_list.sort(key=lambda x: x['start_time'])
        
        result = {"itinerary": itinerary_list}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()