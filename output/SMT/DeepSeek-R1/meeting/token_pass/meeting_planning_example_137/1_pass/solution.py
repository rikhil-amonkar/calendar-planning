import z3
import json

def main():
    # Convert time to minutes since 8:00 AM
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return (hour - 8) * 60 + minute

    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = total_minutes // 60 + 8
        minute = total_minutes % 60
        return f"{hour}:{minute:02d}"

    # Travel times in minutes
    travel_times = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Golden Gate Park"): 23,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23
    }

    # Convert constraint times to minutes
    start_time_fd = time_to_minutes("9:00")  # 60 minutes
    kenneth_available_start = time_to_minutes("12:00")  # 240 minutes
    kenneth_available_end = time_to_minutes("15:00")  # 420 minutes
    barbara_available_start = time_to_minutes("8:15")  # 15 minutes
    barbara_available_end = time_to_minutes("19:00")  # 660 minutes
    kenneth_min_duration = 90
    barbara_min_duration = 45

    # Create solver instance
    solver = z3.Optimize()

    # Meeting time variables
    k_start = z3.Int('k_start')
    k_end = z3.Int('k_end')
    b_start = z3.Int('b_start')
    b_end = z3.Int('b_end')

    # Order variables: 0 for Kenneth first, 1 for Barbara first
    order = z3.Int('order')

    # Add constraints for both meetings
    solver.add(k_start >= kenneth_available_start)
    solver.add(k_end <= kenneth_available_end)
    solver.add(k_end - k_start >= kenneth_min_duration)
    
    solver.add(b_start >= barbara_available_start)
    solver.add(b_end <= barbara_available_end)
    solver.add(b_end - b_start >= barbara_min_duration)

    # Constraints based on order
    # Order 0: FD -> CT -> GGP
    cond0 = z3.And(
        order == 0,
        k_start >= start_time_fd + travel_times[("Financial District", "Chinatown")],
        b_start >= k_end + travel_times[("Chinatown", "Golden Gate Park")]
    )
    
    # Order 1: FD -> GGP -> CT
    cond1 = z3.And(
        order == 1,
        b_start >= start_time_fd + travel_times[("Financial District", "Golden Gate Park")],
        k_start >= b_end + travel_times[("Golden Gate Park", "Chinatown")]
    )
    
    solver.add(z3.Or(cond0, cond1))

    # Try to maximize the number of meetings first, then minimize total time
    solver.maximize(k_end - k_start + b_end - b_start)
    
    if solver.check() == z3.sat:
        model = solver.model()
        k_start_val = model.eval(k_start).as_long()
        k_end_val = model.eval(k_end).as_long()
        b_start_val = model.eval(b_start).as_long()
        b_end_val = model.eval(b_end).as_long()
        
        itinerary = [
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": minutes_to_time(k_start_val),
                "end_time": minutes_to_time(k_end_val)
            },
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": minutes_to_time(b_start_val),
                "end_time": minutes_to_time(b_end_val)
            }
        ]
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()