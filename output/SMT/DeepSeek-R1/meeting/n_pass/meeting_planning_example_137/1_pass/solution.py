import z3
import json

def main():
    solver = z3.Optimize()
    
    # Define variables (in minutes from midnight)
    T = z3.Int('T')  # Departure time from Financial District
    start_B = z3.Int('start_B')
    end_B = z3.Int('end_B')
    start_K = z3.Int('start_K')
    end_K = z3.Int('end_K')
    is_Barbara_first = z3.Bool('is_Barbara_first')
    
    # Constraints
    solver.add(T >= 540)  # Must leave FD at or after 9:00 AM (540 minutes)
    
    # Meeting durations
    solver.add(end_B == start_B + 45)  # 45 minutes with Barbara
    solver.add(end_K == start_K + 90)  # 90 minutes with Kenneth
    
    # Availability constraints
    solver.add(start_B >= 495)   # Barbara available from 8:15 AM (495 minutes)
    solver.add(end_B <= 1140)    # Barbara available until 7:00 PM (1140 minutes)
    solver.add(start_K >= 720)   # Kenneth available from 12:00 PM (720 minutes)
    solver.add(end_K <= 900)     # Kenneth available until 3:00 PM (900 minutes)
    
    # Order and travel constraints
    solver.add(z3.Or(
        z3.And(is_Barbara_first, start_B >= T + 23, start_K >= end_B + 23),
        z3.And(z3.Not(is_Barbara_first), start_K >= T + 5, start_B >= end_K + 23)
    ))
    
    # Define the end time of the last meeting
    last_end = z3.Int('last_end')
    solver.add(last_end == z3.If(is_Barbara_first, end_K, end_B))
    solver.minimize(last_end)
    
    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        T_val = model[T].as_long()
        start_B_val = model[start_B].as_long()
        end_B_val = model[end_B].as_long()
        start_K_val = model[start_K].as_long()
        end_K_val = model[end_K].as_long()
        is_Barbara_first_val = z3.is_true(model[is_Barbara_first])
        
        # Convert minutes to HH:MM format
        def to_time_str(total_minutes):
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"
        
        # Create itinerary in chronological order
        itinerary = []
        if is_Barbara_first_val:
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": to_time_str(start_B_val),
                "end_time": to_time_str(end_B_val)
            })
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": to_time_str(start_K_val),
                "end_time": to_time_str(end_K_val)
            })
        else:
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": to_time_str(start_K_val),
                "end_time": to_time_str(end_K_val)
            })
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": to_time_str(start_B_val),
                "end_time": to_time_str(end_B_val)
            })
        
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()