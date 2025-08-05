import z3
import json

def main():
    # Convert times to minutes from 9:00 AM
    kenneth_start_min = (14 - 9) * 60 + 15   # 14:15 is 315 minutes from 9:00 AM
    kenneth_end_min = (19 - 9) * 60 + 45     # 19:45 is 645 minutes from 9:00 AM

    # Initialize the optimizer
    opt = z3.Optimize()
    T_leave = z3.Int('T_leave')
    S = z3.Int('S')
    E = z3.Int('E')

    # Add constraints
    opt.add(T_leave >= 0)
    opt.add(S >= T_leave + 11)
    opt.add(S >= kenneth_start_min)
    opt.add(E == S + 90)
    opt.add(E <= kenneth_end_min)
    opt.minimize(S)

    # Check for a solution
    if opt.check() == z3.sat:
        m = opt.model()
        s_val = m.eval(S).as_long()
        e_val = m.eval(E).as_long()
        
        # Convert minutes back to HH:MM format
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        end_hour = 9 + e_val // 60
        end_minute = e_val % 60
        
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        itinerary = [{
            "action": "meet",
            "person": "Kenneth",
            "start_time": start_time,
            "end_time": end_time
        }]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()