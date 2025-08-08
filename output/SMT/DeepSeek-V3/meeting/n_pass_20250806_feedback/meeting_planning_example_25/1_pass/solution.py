from z3 import *
import json

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define the variables
    # Start time of the meeting with David (in minutes since 9:00 AM)
    start_time = Int('start_time')
    
    # Convert all times to minutes since 9:00 AM for easier arithmetic
    # You arrive at Golden Gate Park at 9:00 AM (0 minutes)
    # David is available from 4:00 PM to 9:45 PM
    david_start = (16 * 60) - (9 * 60)  # 4:00 PM is 16:00, so 420 minutes since 9:00 AM
    david_end = (21 * 60 + 45) - (9 * 60)  # 9:45 PM is 21:45, so 765 minutes since 9:00 AM
    
    # Travel time to Chinatown is 23 minutes
    travel_time = 23
    
    # Meeting duration must be at least 105 minutes
    meeting_duration = 105
    
    # Constraints:
    # 1. You can't leave Golden Gate Park before 9:00 AM (0 minutes)
    # 2. The earliest you can arrive at Chinatown is 4:00 PM (david_start)
    #    So the earliest you can leave Golden Gate Park is david_start - travel_time
    earliest_departure = david_start - travel_time
    s.add(start_time >= earliest_departure)
    
    # 3. The latest you can arrive at Chinatown is 9:45 PM (david_end)
    #    But the meeting must last at least 105 minutes, so the latest you can start is david_end - meeting_duration
    latest_start = david_end - meeting_duration
    s.add(start_time <= latest_start)
    
    # 4. The meeting must start no earlier than david_start (4:00 PM)
    #    Because you can't meet David before he arrives
    s.add(start_time + travel_time >= david_start)
    
    # We want to maximize the meeting time, so we'll pick the earliest possible start time
    # This is because the problem asks to meet as many friends as possible, so we should free up time later
    # Here, we just need to find a feasible solution, so we'll pick the earliest start time
    s.push()
    s.add(start_time == earliest_departure)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert back to HH:MM format
        total_minutes_since_9am = start_minutes + travel_time
        hours_since_9am = total_minutes_since_9am // 60
        minutes_since_hour = total_minutes_since_9am % 60
        start_hour = 9 + hours_since_9am
        start_time_str = f"{start_hour:02d}:{minutes_since_hour:02d}"
        
        # Calculate end time
        end_minutes_since_9am = total_minutes_since_9am + meeting_duration
        hours_since_9am_end = end_minutes_since_9am // 60
        minutes_since_hour_end = end_minutes_since_9am % 60
        end_hour = 9 + hours_since_9am_end
        end_time_str = f"{end_hour:02d}:{minutes_since_hour_end:02d}"
        
        # Create the itinerary
        itinerary = [
            {"action": "meet", "person": "David", "start_time": start_time_str, "end_time": end_time_str}
        ]
        
        # Output the result
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No feasible schedule found.")

solve_scheduling()