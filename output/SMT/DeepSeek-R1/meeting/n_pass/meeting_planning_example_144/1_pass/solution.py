import z3

def main():
    s = z3.Solver()
    
    # Convert times to minutes from 9:00 AM
    # Laura: 12:15 PM to 7:45 PM -> 195 to 645 minutes
    # Anthony: 12:30 PM to 2:45 PM -> 210 to 345 minutes
    laura_avail_start = 195
    laura_avail_end = 645
    anthony_avail_start = 210
    anthony_avail_end = 345
    
    # Travel times in minutes
    castro_to_mission = 7
    castro_to_financial = 20
    mission_to_financial = 17
    financial_to_mission = 17
    
    # Define variables
    start_L = z3.Int('start_L')
    start_A = z3.Int('start_A')
    order = z3.Int('order')  # 0: Laura first, 1: Anthony first
    
    # Order must be either 0 or 1
    s.add(z3.Or(order == 0, order == 1))
    
    # Meeting duration constraints
    s.add(start_L >= laura_avail_start)
    s.add(start_L + 75 <= laura_avail_end)
    s.add(start_A >= anthony_avail_start)
    s.add(start_A + 30 <= anthony_avail_end)
    
    # Constraints based on meeting order
    s.add(z3.If(order == 0,
                z3.And(
                    start_L >= castro_to_mission,
                    start_A >= start_L + 75 + mission_to_financial
                ),
                z3.And(
                    start_A >= castro_to_financial,
                    start_L >= start_A + 30 + financial_to_mission
                )
            ))
    
    # Check for a solution
    if s.check() == z3.sat:
        m = s.model()
        start_L_val = m[start_L].as_long()
        start_A_val = m[start_A].as_long()
        
        # Create meeting entries
        meetings = []
        meetings.append(("Laura", start_L_val, start_L_val + 75))
        meetings.append(("Anthony", start_A_val, start_A_val + 30))
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[1])
        
        itinerary = []
        for person, start_min, end_min in meetings:
            # Convert start time
            start_hours = 9 + start_min // 60
            start_minutes = start_min % 60
            start_time = f"{start_hours:02d}:{start_minutes:02d}"
            
            # Convert end time
            end_hours = 9 + end_min // 60
            end_minutes = end_min % 60
            end_time = f"{end_hours:02d}:{end_minutes:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_time,
                "end_time": end_time
            })
        
        # Output the solution
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()